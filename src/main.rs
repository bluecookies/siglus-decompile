// TODO: attach opcode addresses to instructions in basic blocks
// 	check if a target address is already inside a basic block
//	and split it if so


// TODO: cleaning
// Stack frame into one struct
// Move to different modules
// TODO: actually look for the TODO's to fix
// 	need to actually fix them

// TODO: handle procedures

extern crate getopts;
extern crate byteorder;
extern crate itertools;
extern crate petgraph;


#[macro_use]
extern crate log;
extern crate fern;

use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Cursor, Write};
use byteorder::{LittleEndian, ReadBytesExt};

use getopts::Options;

type Result<T> = std::result::Result<T, Box<std::error::Error>>;


mod cfg;
mod expression;
use cfg::{ControlFlowGraph, Instruction, Statement};
use expression::{Expression, BinaryOp, FunctionType};


#[derive(Debug)]
struct HeaderPair {
	offset: u32,
	count: u32
}

#[derive(Debug)]
struct ScenePackHeader {
	header_size: u32,

	global_var_types: HeaderPair,
	global_var_name_table: HeaderPair,
	global_var_name_data: HeaderPair,

	global_func_location: HeaderPair,
	global_func_name_table: HeaderPair,
	global_func_name_data: HeaderPair,

	scene_name_table: HeaderPair,
	scene_name_data: HeaderPair,

	scene_data_table: HeaderPair,
	scene_data: HeaderPair,

	extra_key_use: bool,
	source_header_length: u32,	// length of the first unknown block
}

impl ScenePackHeader {
	fn read_global_vars<R>(&self, scene_pack: &mut R) -> Result<Vec<Variable>> where R: ReadBytesExt + Seek {
		let mut var_types: Vec<(u32, usize)> = Vec::with_capacity(self.global_var_types.count as usize);
		scene_pack.seek(SeekFrom::Start(self.global_var_types.offset as u64)).expect("Could not seek.");
		for _ in 0..self.global_var_types.count {
			let var_type = scene_pack.read_u32::<LittleEndian>()?;
			let var_length = scene_pack.read_u32::<LittleEndian>()? as usize;
			var_types.push((var_type, var_length));
		}

		let var_names = read_strings(scene_pack, &self.global_var_name_table, &self.global_var_name_data)?;

		if var_names.len() != var_types.len() {
			return Err("Global variables count mismatch.".into());
		}

		Ok(zip(var_names, var_types).map(|(name, var_type)| {
			Variable {
				name,
				var_type: VariableType::from_pair(var_type).expect("Could not extract type")
			}
		}).collect())
	}

	fn read_global_funcs<R>(&self, scene_pack: &mut R) -> Result<Vec<Function>> where R: ReadBytesExt + Seek {
		let mut func_locations: Vec<(usize, usize)> = Vec::with_capacity(self.global_func_location.count as usize);
		scene_pack.seek(SeekFrom::Start(self.global_func_location.offset as u64)).expect("Could not seek.");
		for _ in 0..self.global_func_location.count {
			let file_index = scene_pack.read_u32::<LittleEndian>()? as usize;
			let offset = scene_pack.read_u32::<LittleEndian>()? as usize;
			func_locations.push((file_index, offset));
		}
		let func_names = read_strings(scene_pack, &self.global_func_name_table, &self.global_func_name_data)?;

		if func_names.len() != func_locations.len() {
			return Err("Global functions count mismatch.".into());
		}

		Ok(zip(func_names, func_locations).map(|(name, (file_index, offset))| {
			Function {
				name,
				file_index: Some(file_index),
				offset
			}
		}).collect())
	}
}

// struct ScenePackData

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum VariableType {
	Void,	//0x00
	Int,	//0x0a
	IntList(usize),	//0x0b
	IntRef,	//0x0d
	Str,	//0x14
	StrList(usize),	//0x15
	StrRef,	//0x17
	Obj,	//0x51e
	ObjList(usize),
	StageElem,
	Error,
	Unknown,
}

#[derive(Debug, Clone)]
pub struct Variable {
	name: String,
	var_type: VariableType,
}

// TODO: turn the expression type into a wrapper around this one
impl Variable {
	fn to_expression(&self) -> Expression {
		Expression::Variable {
			name: self.name.clone(),
			var_type: self.var_type
		}
	}
}

impl std::fmt::Display for Variable {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{} {}", self.var_type, self.name)
	}
}

// TODO: fold this into function expressions (as a command or something)
#[derive(Debug, Clone)]
pub struct Function {
	name: String,
	file_index: Option<usize>,
	offset: usize,	// in bytes
}

impl Function {
	fn to_expression(&self) -> Expression {
		Expression::Function(FunctionType::Named(self.name.clone()))
	}
}

impl VariableType {
	// TODO: check this is good
	fn from_pair((var_type, length): (u32, usize)) -> Result<VariableType> {
		match var_type {
			0x0a => if length == 0 { Ok(VariableType::Int) } else { Err("Int variable cannot have a length.".into()) },
			0x0b => Ok(VariableType::IntList(length)),
			0x14 => if length == 0 { Ok(VariableType::Str) } else { Err("Str variable cannot have a length.".into()) },
			0x15 => Ok(VariableType::StrList(length)),
			_ => Err(format!("Unexpected var type {:#x}", var_type).into())
		}
	}

	fn from_u32(var_type: u32) -> VariableType {
		match var_type {
			0x00 => VariableType::Void,
			0x0a => VariableType::Int,
			0x0b => VariableType::IntList(0),
			0x0d => VariableType::IntRef,
			0x14 => VariableType::Str,
			0x15 => VariableType::StrList(0),
			0x17 => VariableType::StrRef,
			0x51e => VariableType::Obj,
			0x514 => VariableType::StageElem,
			_ => {
				warn!("Unexpected var type {:#x}", var_type);
				VariableType::Unknown
			}
		}
	}

	fn is_list(&self) -> bool {
		match *self {
			VariableType::IntList(_) | 
			VariableType::StrList(_) | 
			VariableType::ObjList(_) => true,
			_ => false,
		}
	}

	fn set_length(&mut self, length: usize) {
		match self {
			VariableType::IntList(ref mut len) | 
			VariableType::StrList(ref mut len) | 
			VariableType::ObjList(ref mut len) => *len = length,
			_ => warn!("Type {:?} has no length.", self),
		}
	} 
}

impl std::fmt::Display for VariableType {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			VariableType::Void => write!(f, "void"),
			VariableType::Int => write!(f, "int"),
			VariableType::IntList(len) => write!(f, "int[{}]", len),
			VariableType::IntRef => write!(f, "&int"),
			VariableType::Str => write!(f, "str"),
			VariableType::StrList(len) => write!(f, "str[{}]", len),
			VariableType::StrRef => write!(f, "&str"),
			VariableType::Obj => write!(f, "obj"),
			VariableType::ObjList(len) => write!(f, "obj[{}]", len),
			VariableType::StageElem => write!(f, "stage_elem"),
			VariableType::Error => write!(f, "ERROR"),
			VariableType::Unknown => write!(f, "???"),
		}
	}
}

// TODO: add lists (0xFFFFFFFF)
fn read_args<R>(reader: &mut R, stack: &mut ProgStack) -> Result<Vec<Expression>> where R: ReadBytesExt {
	let num_args = reader.read_u32::<LittleEndian>()?;

	let mut args = Vec::new();
	for _ in 0..num_args {
		let type_num = reader.read_u32::<LittleEndian>()?;
		if type_num == 0xFFFFFFFF {
			let list = read_args(reader, stack)?;
			args.push(Expression::List(list));
		} else {
			let arg_type = VariableType::from_u32(type_num);

			args.push(stack.get_value(arg_type));
		}
	}

	Ok(args)
}

fn print_usage(program: &str, opts: Options) {
	let brief = format!("Usage: {} [-k xorkey] [Scene.pck]", program);
	println!("{}", opts.usage(&brief));
}

fn setup_logger() -> Result<()> {
	fern::Dispatch::new()
		.format(|out, message, record| {
			out.finish(format_args!(
				"[{}][{}] {}",
				record.target(),
				record.level(),
				message
			))
		})
		.chain(
			fern::Dispatch::new()
				.level(log::LevelFilter::Debug)
				.chain(std::io::stdout())
		)
		.chain(
			fern::Dispatch::new()
				.level(log::LevelFilter::Trace)
				//.level_for("siglus_decompile", log::LevelFilter::Trace)
				.chain(std::fs::OpenOptions::new()
					.write(true)
					.create(true)
					.truncate(true)
					.open("output.log")?
				)
		)
		.apply()?;
	Ok(())
}

fn main() {
	let mut args = std::env::args();
	let prog_name = args.next().unwrap();

	let mut opts = Options::new();
	opts.optopt("k", "key", "key file to be used for decryption", "xorkey");
	opts.optopt("s", "scene", "decompile specific scene", "scenename");
	opts.optopt("m", "macro", "file containing macro rules for replacement", "macro_rules");
	opts.optflag("h", "help", "print this help menu");
	let matches = opts.parse(args).unwrap();
	if matches.opt_present("h") {
		print_usage(&prog_name, opts);
		return;
	}
	if matches.free.len() > 1 {
		print_usage(&prog_name, opts);
		return;
	}

	// Read decryption key if provided
	let decrypt_key: Option<Vec<u8>> = matches.opt_str("k").map(|keyfile| {
		let mut keyfile = File::open(keyfile).expect("Could not open key!");
		let mut key:Vec<u8> = vec![0; 16];
		keyfile.read_exact(key.as_mut_slice()).expect("Could not read key!");

		key
	});

	let target_scene: Option<String> = matches.opt_str("s");

	// Set up logging to stdout and to an output log
	setup_logger().unwrap();

	let filename: &str = matches.free.first().map(String::as_str).unwrap_or("Scene.pck");

	let mut scene_pack = match File::open(filename) {
		Ok(v) => v,
		Err(e) => {
			eprintln!("Could not open scene pack! Error: {}", e);
			return;
		}
	};

	let scene_pack_header = read_scene_pack_header(&mut scene_pack).expect("Error reading scene pack header.");

	if decrypt_key.is_some() != scene_pack_header.extra_key_use {
		println!("Error: key (not) expected");
		return;
	}

	// Read global variables
	let global_vars: Vec<Variable> = scene_pack_header.read_global_vars(&mut scene_pack).unwrap(); 

	// Read global functions
	let global_functions: Vec<Function> = scene_pack_header.read_global_funcs(&mut scene_pack).unwrap();

	// Read scenes
	let scene_names: Vec<String> = read_strings(&mut scene_pack, &scene_pack_header.scene_name_table, &scene_pack_header.scene_name_data).unwrap();
	let mut scene_data_table: Vec<HeaderPair> = Vec::with_capacity(scene_pack_header.scene_data_table.count as usize);
	scene_pack.seek(SeekFrom::Start(scene_pack_header.scene_data_table.offset as u64)).unwrap();
	for _ in 0..scene_pack_header.scene_data_table.count {
		scene_data_table.push(read_header_pair(&mut scene_pack).unwrap());
	}

	if scene_names.len() != scene_data_table.len() {
		println!("Scene names and data length mismatch");
		return;
	}

	if let Some(ref name) = target_scene {
		if !scene_names.contains(name) {
			error!("Target scene {} does not exist!", name);
			return;
		}
	}

	std::fs::create_dir_all("Scene").expect("Could not create output directory!");

	info!("Parsing {} scenes.", scene_names.len());
	debug!("{:?}", scene_names);

	// TODO: remove the take
	let scene_table = {
		zip(scene_names, scene_data_table).filter(|&(ref scene_name, _)|
			if let Some(ref name) = target_scene { name == scene_name }
			else { true }
		).take(1)
	};
	for (scene_name, HeaderPair{ offset, count: length }) in scene_table {
		scene_pack.seek(SeekFrom::Start((scene_pack_header.scene_data.offset + offset) as u64)).unwrap();

		let mut buffer: Vec<u8> = vec![0; length as usize];
		scene_pack.read_exact(buffer.as_mut_slice()).unwrap();

		if let Some(ref key) = decrypt_key {
			for (value, key) in buffer.iter_mut().zip(key.iter().cycle()) {
				*value ^= *key;
			}
		}

		decrypt_scene(buffer.as_mut_slice());

		let (compressed_size, decompressed_size) = {
			let mut buffer = buffer.as_slice();
			let comp = buffer.read_u32::<LittleEndian>().unwrap();
			let decomp = buffer.read_u32::<LittleEndian>().unwrap() as usize;
			(comp, decomp)
		};

		if compressed_size != length {
			println!("Error: expected {} bytes, got {}.", length, compressed_size);
			return;
		}

		let decompressed = decompress_lzss_8(&buffer[8..], decompressed_size).expect("Error in decompression");
		
		let script = parse_script(Cursor::new(decompressed), &scene_name).expect("Could not parse script");

		let mut graph_out = File::create(format!("Scene/{}.gv", scene_name)).expect("Could not create output file for writing");

		// Construct file structure
		let source_file = script.decompile(&global_vars, &global_functions, &mut graph_out).expect("Error parsing bytecode.");

		let mut out = File::create(format!("Scene/{}.ss", scene_name)).expect("Could not create output file for writing");
		source_file.write(&mut out).expect("Error writing file.");	
	}
}

fn read_scene_pack_header(scene_pack: &mut File) -> Result<ScenePackHeader> {
	// Read header
	let header_size = scene_pack.read_u32::<LittleEndian>()?;
	if header_size != 0x5C {
		return Err(format!("Expected header size 0x5C, got {:x}", header_size).into());
	}
	let global_var_types = read_header_pair(scene_pack)?;
	let global_var_name_table = read_header_pair(scene_pack)?;
	let global_var_name_data = read_header_pair(scene_pack)?;

	let global_func_location = read_header_pair(scene_pack)?;
	let global_func_name_table = read_header_pair(scene_pack)?;
	let global_func_name_data = read_header_pair(scene_pack)?;

	let scene_name_table = read_header_pair(scene_pack)?;
	let scene_name_data = read_header_pair(scene_pack)?;

	let scene_data_table = read_header_pair(scene_pack)?;
	let scene_data = read_header_pair(scene_pack)?;

	let extra_key_use = scene_pack.read_u32::<LittleEndian>()? != 0;
	let source_header_length = scene_pack.read_u32::<LittleEndian>()?;

	Ok(ScenePackHeader {
		header_size,

		global_var_types,
		global_var_name_table,
		global_var_name_data,
		global_func_location,
		global_func_name_table,
		global_func_name_data,
		scene_name_table,
		scene_name_data,
		scene_data_table,
		scene_data,

		extra_key_use,
		source_header_length,
	})
}

fn read_header_pair<R>(reader: &mut R) -> Result<HeaderPair> where R: ReadBytesExt {
	let offset = reader.read_u32::<LittleEndian>()?;
	let count = reader.read_u32::<LittleEndian>()?;
	Ok(HeaderPair {
		offset,
		count
	})
}

fn read_strings<R>(reader: &mut R, index: &HeaderPair, data: &HeaderPair) -> Result<Vec<String>> where R: ReadBytesExt + Seek {
	if index.count != data.count {
		return Err("Index and string data length mismatch.".into());
	}

	let mut index_table: Vec<HeaderPair> = Vec::with_capacity(index.count as usize);
	reader.seek(SeekFrom::Start(index.offset as u64))?;
	for _ in 0..index.count {
		index_table.push(read_header_pair(reader)?);
	}

	let mut strings = Vec::with_capacity(data.count as usize);
	for i in 0..data.count as usize {
		let HeaderPair { offset, count } = index_table[i];
		reader.seek(SeekFrom::Start((data.offset + 2 * offset) as u64))?;

		let mut raw_utf16: Vec<u16> = vec![0; count as usize];
		reader.read_u16_into::<LittleEndian>(raw_utf16.as_mut_slice())?;
		strings.push(String::from_utf16(&raw_utf16)?);
	}

	Ok(strings)
}

fn read_strings_with_key<R>(reader: &mut R, index: &HeaderPair, data: &HeaderPair, key: u16) -> Result<Vec<String>> where R: ReadBytesExt + Seek {
	if index.count != data.count {
		return Err("Index and string data length mismatch.".into());
	}

	let mut index_table: Vec<HeaderPair> = Vec::with_capacity(index.count as usize);
	reader.seek(SeekFrom::Start(index.offset as u64))?;
	for _ in 0..index.count {
		index_table.push(read_header_pair(reader)?);
	}

	let mut strings = Vec::with_capacity(data.count as usize);
	for i in 0..data.count as usize {
		let HeaderPair { offset, count } = index_table[i];
		reader.seek(SeekFrom::Start((data.offset + 2 * offset) as u64))?;

		let mut raw_utf16: Vec<u16> = vec![0; count as usize];
		reader.read_u16_into::<LittleEndian>(raw_utf16.as_mut_slice())?;
		for ch in raw_utf16.as_mut_slice() {
			*ch ^= (i as u16).wrapping_mul(key);
		}
		strings.push(String::from_utf16(&raw_utf16)?);
	}

	Ok(strings)
}

fn read_labels<R>(reader: &mut R, index: &HeaderPair) -> Result<Vec<usize>> where R: ReadBytesExt + Seek {
	let mut v: Vec<usize> = Vec::with_capacity(index.count as usize);

	reader.seek(SeekFrom::Start(index.offset as u64))?;
	for _ in 0..index.count {
		v.push(reader.read_u32::<LittleEndian>()? as usize);
	}
	
	Ok(v)
}

static XOR_KEY: [u8; 256] = [
	0x70, 0xF8, 0xA6, 0xB0, 0xA1, 0xA5, 0x28, 0x4F, 0xB5, 0x2F, 0x48, 0xFA, 0xE1, 0xE9, 0x4B, 0xDE,
	0xB7, 0x4F, 0x62, 0x95, 0x8B, 0xE0, 0x03, 0x80, 0xE7, 0xCF, 0x0F, 0x6B, 0x92, 0x01, 0xEB, 0xF8,
	0xA2, 0x88, 0xCE, 0x63, 0x04, 0x38, 0xD2, 0x6D, 0x8C, 0xD2, 0x88, 0x76, 0xA7, 0x92, 0x71, 0x8F,
	0x4E, 0xB6, 0x8D, 0x01, 0x79, 0x88, 0x83, 0x0A, 0xF9, 0xE9, 0x2C, 0xDB, 0x67, 0xDB, 0x91, 0x14,
	0xD5, 0x9A, 0x4E, 0x79, 0x17, 0x23, 0x08, 0x96, 0x0E, 0x1D, 0x15, 0xF9, 0xA5, 0xA0, 0x6F, 0x58,
	0x17, 0xC8, 0xA9, 0x46, 0xDA, 0x22, 0xFF, 0xFD, 0x87, 0x12, 0x42, 0xFB, 0xA9, 0xB8, 0x67, 0x6C,
	0x91, 0x67, 0x64, 0xF9, 0xD1, 0x1E, 0xE4, 0x50, 0x64, 0x6F, 0xF2, 0x0B, 0xDE, 0x40, 0xE7, 0x47,
	0xF1, 0x03, 0xCC, 0x2A, 0xAD, 0x7F, 0x34, 0x21, 0xA0, 0x64, 0x26, 0x98, 0x6C, 0xED, 0x69, 0xF4,
	0xB5, 0x23, 0x08, 0x6E, 0x7D, 0x92, 0xF6, 0xEB, 0x93, 0xF0, 0x7A, 0x89, 0x5E, 0xF9, 0xF8, 0x7A,
	0xAF, 0xE8, 0xA9, 0x48, 0xC2, 0xAC, 0x11, 0x6B, 0x2B, 0x33, 0xA7, 0x40, 0x0D, 0xDC, 0x7D, 0xA7,
	0x5B, 0xCF, 0xC8, 0x31, 0xD1, 0x77, 0x52, 0x8D, 0x82, 0xAC, 0x41, 0xB8, 0x73, 0xA5, 0x4F, 0x26,
	0x7C, 0x0F, 0x39, 0xDA, 0x5B, 0x37, 0x4A, 0xDE, 0xA4, 0x49, 0x0B, 0x7C, 0x17, 0xA3, 0x43, 0xAE,
	0x77, 0x06, 0x64, 0x73, 0xC0, 0x43, 0xA3, 0x18, 0x5A, 0x0F, 0x9F, 0x02, 0x4C, 0x7E, 0x8B, 0x01,
	0x9F, 0x2D, 0xAE, 0x72, 0x54, 0x13, 0xFF, 0x96, 0xAE, 0x0B, 0x34, 0x58, 0xCF, 0xE3, 0x00, 0x78,
	0xBE, 0xE3, 0xF5, 0x61, 0xE4, 0x87, 0x7C, 0xFC, 0x80, 0xAF, 0xC4, 0x8D, 0x46, 0x3A, 0x5D, 0xD0,
	0x36, 0xBC, 0xE5, 0x60, 0x77, 0x68, 0x08, 0x4F, 0xBB, 0xAB, 0xE2, 0x78, 0x07, 0xE8, 0x73, 0xBF
];

fn decrypt_scene(buffer: &mut [u8]) {
	for (i, value) in buffer.iter_mut().enumerate() {
		*value ^= XOR_KEY[i % 256];
	}
}

fn decompress_lzss_8(mut compressed: &[u8], size: usize) -> Result<Vec<u8>> {
	let mut decompressed = Vec::with_capacity(size);

	'decomp: loop {
		if compressed.is_empty() {
			break 'decomp;
		}

		let marker = compressed.read_u8()?;
		for i in 0..8 {
			if compressed.is_empty() {
				break 'decomp;
			}
			if marker & (1 << i) == 0 {
				let counter = compressed.read_u16::<LittleEndian>()? as usize;
				let (counter, offset) = ((counter & 0xF) + 2, counter >> 4);

				// Note: this is not equivalent to a memmove
				for _ in 0..counter {
					let value = decompressed[decompressed.len() - offset];
					decompressed.push(value);
				}
			} else {
				decompressed.push(compressed.read_u8()?);
			}
		}
	}

	Ok(decompressed)
}

////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
struct Script {
	name: String,

	bytecode: Vec<u8>,

	labels: Vec<usize>,
	entrypoints: Vec<usize>,
	// Pairs of (Function index, file offset)
	function_index: Vec<(usize, usize)>,

	strings: Vec<String>,

	static_vars: Vec<Variable>,
	static_funcs: Vec<Function>,

	local_var_names: Vec<String>,
}

#[derive(Debug)]
struct ScriptHeader {
	header_size: u32,

	bytecode_index: HeaderPair,

	string_table: HeaderPair,
	string_data: HeaderPair,

	labels: HeaderPair,
	entrypoints: HeaderPair,
	function_locations: HeaderPair,

	static_var_types: HeaderPair,
	static_var_name_table: HeaderPair,
	static_var_name_data: HeaderPair,

	static_func_location: HeaderPair,
	static_func_name_table: HeaderPair,
	static_func_name_data: HeaderPair,

	local_var_name_table: HeaderPair,
	local_var_name_data: HeaderPair,

	_unknown6: HeaderPair,
	_unknown7: HeaderPair,
}


impl ScriptHeader {
	fn read_static_vars<R>(&self, script: &mut R) -> Result<Vec<Variable>> where R: ReadBytesExt + Seek {
		let mut var_types: Vec<(u32, usize)> = Vec::with_capacity(self.static_var_types.count as usize);
		script.seek(SeekFrom::Start(self.static_var_types.offset as u64)).expect("Could not seek.");
		for _ in 0..self.static_var_types.count {
			let var_type = script.read_u32::<LittleEndian>()?;
			let var_length = script.read_u32::<LittleEndian>()? as usize;
			var_types.push((var_type, var_length));
		}

		let var_names = read_strings(script, &self.static_var_name_table, &self.static_var_name_data)?;

		if var_names.len() != var_types.len() {
			return Err("Static variables count mismatch.".into());
		}

		Ok(zip(var_names, var_types).map(|(name, var_type)| {
			Variable {
				name,
				var_type: VariableType::from_pair(var_type).expect("Could not extract type")
			}
		}).collect())
	}

	fn read_static_funcs<R>(&self, script: &mut R) -> Result<Vec<Function>> where R: ReadBytesExt + Seek {
		let mut func_locations: Vec<usize> = Vec::with_capacity(self.static_func_location.count as usize);
		script.seek(SeekFrom::Start(self.static_func_location.offset as u64)).expect("Could not seek.");
		for _ in 0..self.static_func_location.count {
			let offset = script.read_u32::<LittleEndian>()? as usize;
			func_locations.push(offset);
		}
		let func_names = read_strings(script, &self.static_func_name_table, &self.static_func_name_data)?;

		if func_names.len() != func_locations.len() {
			return Err("Static functions count mismatch.".into());
		}

		Ok(zip(func_names, func_locations).map(|(name, offset)| {
			Function {
				name,
				file_index: None,
				offset,
			}
		}).collect())
	}

}

fn parse_script<R>(mut reader: R, script_name: &str) -> Result<Script> where R: ReadBytesExt + Seek {
	debug!("Parsing script: {}", script_name);

	let script_header = read_script_header(&mut reader)?;

	let strings = read_strings_with_key(&mut reader, &script_header.string_table, &script_header.string_data, 0x7087)?;

	let labels = read_labels(&mut reader, &script_header.labels)?;
	let entrypoints = read_labels(&mut reader, &script_header.entrypoints)?;
	

	let mut function_index = Vec::with_capacity(script_header.function_locations.count as usize);
	reader.seek(SeekFrom::Start(script_header.function_locations.offset as u64))?;
	for _ in 0..script_header.function_locations.count {
		let function_id = reader.read_u32::<LittleEndian>()? as usize;
		let offset = reader.read_u32::<LittleEndian>()? as usize;

		function_index.push((function_id, offset));
		trace!("Function {:#x} at {:#x}", function_id, offset);
	}
	

	let static_vars = script_header.read_static_vars(&mut reader)?;
	debug!("\tRead {} static variables.", static_vars.len());

	let static_funcs = script_header.read_static_funcs(&mut reader)?;
	debug!("\tRead {} static functions.", static_funcs.len());

	let local_var_names = read_strings(&mut reader, &script_header.local_var_name_table, &script_header.local_var_name_data)?;
	debug!("\tRead {} local variable names.", local_var_names.len());

	// Read bytecode
	let mut bytecode: Vec<u8> = vec![0; script_header.bytecode_index.count as usize];
	reader.seek(SeekFrom::Start(script_header.bytecode_index.offset as u64))?;
	reader.read_exact(bytecode.as_mut_slice())?;

	Ok(Script {
		name: script_name.to_string(),

		bytecode,

		strings,
		labels,
		entrypoints,
		function_index,
		static_vars,
		static_funcs,
		local_var_names,
	})
}

fn read_script_header<R>(script: &mut R) -> Result<ScriptHeader> where R: ReadBytesExt {
	// Read header
	let header_size = script.read_u32::<LittleEndian>()?;
	if header_size != 0x84 {
		return Err(format!("Expected header size 0x84, got {:x}", header_size).into());
	}
	let bytecode_index = read_header_pair(script)?;
	
	let string_table = read_header_pair(script)?;
	let string_data = read_header_pair(script)?;

	let labels = read_header_pair(script)?;
	let entrypoints = read_header_pair(script)?;	// "z levels"
	let function_locations = read_header_pair(script)?;	// offsets of all functions defined in this file

	let static_var_types = read_header_pair(script)?;
	let static_var_name_table = read_header_pair(script)?;
	let static_var_name_data = read_header_pair(script)?;

	let static_func_location = read_header_pair(script)?;
	let static_func_name_table = read_header_pair(script)?;
	let static_func_name_data = read_header_pair(script)?;

	let local_var_name_table = read_header_pair(script)?;
	let local_var_name_data = read_header_pair(script)?;

	let _unknown6 = read_header_pair(script)?;
	let _unknown7 = read_header_pair(script)?;

	Ok(ScriptHeader {
		header_size,

		bytecode_index,

		string_table,
		string_data,

		labels,
		entrypoints,
		function_locations,

		static_var_types,
		static_var_name_table,
		static_var_name_data,

		static_func_location,
		static_func_name_table,
		static_func_name_data,

		local_var_name_table,
		local_var_name_data,

		_unknown6,
		_unknown7,
	})
}

impl Script {
	fn decompile<F: Write>(&self, global_vars: &Vec<Variable>, global_funcs: &Vec<Function>, graph_out: &mut F) -> Result<SourceFile> {
		// Create function index from global functions + static functions
		let mut function_table = global_funcs.to_vec();
		function_table.extend_from_slice(&self.static_funcs);

		let mut global_var_table = global_vars.to_vec();
		global_var_table.extend_from_slice(&self.static_vars);

		let main = {
			// z_level, address
			let entrypoints: Vec<(usize, usize)> = self.entrypoints.iter().cloned().enumerate().filter(|&(_, address)| address != 0).collect();

			let mut graph = ControlFlowGraph::main(&entrypoints);

			// Vec<(address, stack)>
			let mut block_list = entrypoints.into_iter().rev().map(|(_, address)| (address, ProgStack::new())).collect();

			// Parse the bytecode to construct the control flow graph
			self.parse_bytecode(block_list, &mut graph)?;

			graph.replace_ref(&global_var_table, &function_table, &[]);

			graph.write_graph(graph_out).unwrap_or_else(|e| error!("{}", e));

			// Structure loops and two ways and everything else
			graph.structure_statements()
		};

		let mut functions = Vec::new();
		for &(index, address) in self.function_index.iter() {
			let mut graph = ControlFlowGraph::function(address);

			let mut block_list = vec![(address, ProgStack::new())];

			let (num_params, mut local_vars) = self.parse_bytecode(block_list, &mut graph)?.unwrap();

			graph.replace_ref(&global_var_table, &function_table, &local_vars);


			let block = graph.structure_statements();

			local_vars.truncate(num_params);

			let prototype = FunctionPrototype {
				name: function_table[index].name.clone(),
				parameters: local_vars
			};

			functions.push((prototype, block));
		}


		let source = SourceFile {
			main,
			functions,
		};

		Ok(source)
	}

	// If parsing a function, returns Some((num_params, local var list))
	fn parse_bytecode(&self, mut block_list: Vec<(usize, ProgStack)>, graph: &mut ControlFlowGraph) -> Result<Option<(usize, Vec<Variable>)>> {
		let mut bytecode = Cursor::new(&self.bytecode);

		let mut params_done = false;
		let mut num_params = 0;

		// List of parameters + local variables
		// Kept in a single array for ease of access
		let mut local_vars = Vec::new();

		while let Some((block_address, mut stack)) = block_list.pop() {
			let block_id = graph.get_block_id_at(block_address);

			if graph.traversed(block_id) {
				continue;
			} else {
				graph.set_traversed(block_id);
			}

			bytecode.seek(SeekFrom::Start(block_address as u64))?;
			//debug!("\tParsing block {} at {:#x}", block_id, block_address);

			'block_loop: loop {
				let address = bytecode.position() as usize;
				let opcode = bytecode.read_u8()?;
				//debug!("\t\tParsing opcode: {:#02x}", opcode);
				match opcode {
					// Line number - debugging purposes
					0x01 => graph.add_inst(block_id, Instruction::Line(bytecode.read_u32::<LittleEndian>()?)),
					// Push
					0x02 => {
						let value_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						let value = bytecode.read_u32::<LittleEndian>()?;
						stack.push(match value_type {
							VariableType::Int => Expression::RawInt(value as i32),
							VariableType::Str => Expression::RawString(self.strings[value as usize].clone()),
							_ => panic!("Unexpected value type pushed at address {:#x}: {:?}", address, value_type),
						});
					},
					// Pop
					0x03 => {
						let value_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						match value_type {
							VariableType::Void => {},
							VariableType::Int | VariableType::Str => {
								let value = stack.pop(value_type);
								if value.has_side_effect() {
									graph.add_inst(block_id, value.to_inst());
								}
							},
							_ => panic!("Unexpected value type popped at address {:#x}: {:?}", address, value_type),
						}
					},
					// Duplicate
					0x04 => {
						let value_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						match value_type {
							VariableType::Int | VariableType::Str | VariableType::Unknown => {
								let value = stack.pop(value_type);
								// Move the value into a variable if it has side effects
								if value.has_side_effect() {
									let (new_var, inst) = create_variable(value);
									graph.add_inst(block_id, inst);

									stack.push(new_var.clone());
									stack.push(new_var);
								} else {
									stack.push(value.clone());
									stack.push(value);
								}
							},
							_ => panic!("Unexpected value type duplicated at address {:#x}: {:?}", address, value_type),
						}
					},
					// Close frame
					0x05 => {
						let value = stack.handle_frame().unwrap();
						stack.push(value);
					},
					// Duplicate stack frame
					0x06 => stack.dup_frame(),
					// Declare parameter/local variable
					0x07 => {
						let mut var_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						let name_index = bytecode.read_u32::<LittleEndian>()? as usize;
						// Length for lists is on top of the stack
						if var_type.is_list() {
							let length = stack.pop(VariableType::Int);
							if let Expression::RawInt(len) = length {
								var_type.set_length(len as usize);
							} else {
								warn!("Declaring variable of type {:?} - nonconst length ({}) not supported.", var_type, length);
							}
						}

						let var_name = self.local_var_names[name_index].to_string();
						let var = Variable {
							name: var_name,
							var_type
						};
						if params_done {
							graph.add_inst(block_id, Instruction::Expression(var.to_expression()));
						}
						local_vars.push(var);
					},
					// Open frame
					0x08 => stack.open_frame(),
					// Finish declaring parameters
					0x09 => {
						params_done = true;
						num_params = local_vars.len();
					},
					// Jump
					0x10 =>  {
						let jmp_label = bytecode.read_u32::<LittleEndian>()? as usize;
						let jump_address = self.labels[jmp_label];

						let next_block_id = graph.get_block_id_at(jump_address);

						// TODO: check if not traversed/on list already to avoid unnecessary clone
						block_list.push((jump_address, stack.clone()));

						graph.add_successor(block_id, next_block_id);

						break 'block_loop;
					},
					// Jump if (not) zero
					0x11 | 0x12 => {
						let jmp_label = bytecode.read_u32::<LittleEndian>()? as usize;
						let jump_address = self.labels[jmp_label];
						let next_address = bytecode.position() as usize;

						let jump_block_id = graph.get_block_id_at(jump_address);
						let next_block_id = graph.get_block_id_at(next_address);
						
						let value = stack.pop(VariableType::Int);

						let condition = if opcode == 0x12 {
							value.negate()
						} else {
							value
						};

						graph.add_branch(block_id, condition, jump_block_id, next_block_id);

						// Add blocks to list
						block_list.push((jump_address, stack.clone()));
						block_list.push((next_address, stack.clone()));

						break 'block_loop;
					},
					// Short call
					0x13 | 0x14 => {
						let call_label = bytecode.read_u32::<LittleEndian>()? as usize;
						let call_address = self.labels[call_label];

						let call_block = graph.get_block_id_at(call_address);
						// TODO: call_block.is_function = true

						let mut args = read_args(&mut bytecode, &mut stack)?;
						args.reverse();

						// TODO: visit this block
						//block_list.push((call_address, stack.clone()));

						let call = Expression::procedure_call(call_label, args);
						stack.push(call);
					},
					// Return
					0x15 => {
						let mut args = read_args(&mut bytecode, &mut stack)?;
						args.reverse();

						graph.add_inst(block_id, Instruction::Return(args));

						break 'block_loop;
					},
					// End of script
					0x16 => {
						break 'block_loop;
					},
					// Assignment
					0x20 => {
						let _unknown1 = bytecode.read_u32::<LittleEndian>()?;
						let var_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						let _unknown2 = bytecode.read_u32::<LittleEndian>()?;

						let value = stack.pop(var_type);

						let variable = stack.handle_frame().unwrap();

						graph.add_inst(block_id, Instruction::Binding { lhs: variable, rhs: value });
					},
					// Calc1
					0x21 => {
						let var_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						let op = bytecode.read_u8()?;

						if var_type != VariableType::Int {
							panic!("Unknown operation: calc1 {:?} {:#02x}", var_type, op);
						}

						let var = stack.pop(var_type);

						stack.push(Expression::calc1(var, op));
					},
					// Calc2
					0x22 => {
						let type1 = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						let type2 = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);
						let op = bytecode.read_u8()?;

						match (type1, type2) {
							(VariableType::Int, VariableType::Int) =>  {
								let rhs = stack.pop(VariableType::Int);
								let lhs = stack.pop(VariableType::Int);
								stack.push(Expression::calc2_int(lhs, rhs, op));
							},
							(VariableType::Str, VariableType::Str) => {
								let rhs = stack.pop(VariableType::Str);
								let lhs = stack.pop(VariableType::Str);
								stack.push(Expression::calc2_str(lhs, rhs, op));
							},
							(_, _) => panic!("Unknown operation: {:?} {:#02x} {:?}", type1, op, type2),
						}
					},
					// Function call
					0x30 => {
						let option = bytecode.read_u32::<LittleEndian>()?;

						// arguments popped off stack in reverse order
						let mut args = read_args(&mut bytecode, &mut stack)?;
						args.reverse();

						// number of extra parameters
						let num_extra = bytecode.read_u32::<LittleEndian>()?;
						let mut extra_params: Vec<u32> = Vec::new();
						for _ in 0..num_extra {
							extra_params.push(bytecode.read_u32::<LittleEndian>()?);
						}

						let return_type = VariableType::from_u32(bytecode.read_u32::<LittleEndian>()?);

						let function = Box::new(stack.handle_frame().unwrap());

						let extra = if check_function_extra(&function) {
							Some(bytecode.read_u32::<LittleEndian>()?)
						} else { None };

						let call = Expression::FunctionCall{function, option, args, extra_params, return_type, extra};
						if return_type == VariableType::Void {
							graph.add_inst(block_id, Instruction::Expression(call));
						} else {
							stack.push(call);
						}
					},
					// Add text
					0x31 => {
						let text = stack.pop(VariableType::Str);
						let id = bytecode.read_u32::<LittleEndian>()?;
						graph.add_inst(block_id, Instruction::AddText(text, id));
					},
					// Set name
					0x32 => {
						let name = stack.pop(VariableType::Str);
						graph.add_inst(block_id, Instruction::SetName(name));
					},
					_ => panic!("Unexpected opcode at address {:#x}: {:#02x}", address, opcode)
				}

				let new_address = bytecode.position() as usize;
				// Create a new block if next address is labelled
				if self.is_labelled(new_address) {
					block_list.push((new_address, stack));
					let succ =  graph.get_block_id_at(new_address);
					graph.add_successor(block_id, succ);
					break 'block_loop;
				}
			}
		}

		// Return list of parameters if we processed a function
		if params_done {
			Ok(Some((num_params, local_vars)))
		} else {
			Ok(None)
		}
	}

	fn is_labelled(&self, address: usize) -> bool {
		self.labels.contains(&address)
	}
}

//==============================================================================
struct FunctionPrototype {
	name: String,
	// list of parameters (type, name)
	parameters: Vec<Variable>,
	// return type
	// return: Option<VariableType>
}

impl std::fmt::Display for FunctionPrototype {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}({})", self.name, format_list(&self.parameters))
	}
}

struct SourceFile {
	main: Vec<Statement>,

	functions: Vec<(FunctionPrototype, Vec<Statement>)>,
}

impl SourceFile {
	fn write<F: Write>(&self, out: &mut F) -> Result<()> {
		for statement in self.main.iter() {
			statement.write(out, 0)?;
		}
		for &(ref f, ref block) in self.functions.iter() {
			write!(out, "\nfunction {} {{ \n", f)?;
			for statement in block.iter() {
				statement.write(out, 1)?;
			}
			write!(out, "}} \n")?;
		}
		Ok(())
	}
}

////////////////////////////////////////////////////////////////////////////////
#[derive(Clone)]
struct ProgStack {
	values: Vec<Expression>,
	frames: Vec<usize>,
}

impl ProgStack {
	fn new() -> Self {
		ProgStack {
			values: Vec::new(),
			frames: Vec::new(),
		}
	}

	fn pop(&mut self, var_type: VariableType) -> Expression {
		let value = self.values.pop().unwrap();
		let actual_type = value.get_type();

		if actual_type != var_type && var_type != VariableType::Unknown {
			if actual_type == VariableType::Unknown {
				//debug!("Filling in type: {} is {}", value, var_type);
				value
			} else {
				error!("{} - Expected {:?}, got {:?}", value, var_type, actual_type);
				Expression::Error
			}
		} else {
			value
		}
	}

	fn peek_type(&self) -> Option<VariableType> {
		self.values.last().map(|value| value.get_type())
	}

	fn push(&mut self, value: Expression) {
		self.values.push(value);
	}

	fn open_frame(&mut self) {
		self.frames.push(self.values.len());
	}

	fn dup_frame(&mut self) {
		let frame_begin: usize = *self.frames.last().unwrap();
		self.frames.push(self.values.len());

		let mut dup = (&self.values[frame_begin..]).to_vec();
		self.values.append(&mut dup);
	}

	// TODO: better error handling - possible return Result<Option<Expression>> or even Result<Expression>
	fn handle_frame(&mut self) -> Option<Expression> {
		let depth = self.frames.pop().unwrap();
		let frame = self.values.split_off(depth);

		let mut iter = frame.into_iter();
		let mut value = if let Some(Expression::RawInt(value)) =  iter.next() {
			let (value_type, index) = (value >> 24, (value & 0x00FFFFFF) as usize);
			match value_type {
				0x00 => {
					// TODO: figure out a better place to handle this
					if index == 0x53 {
						if let Some(Expression::RawInt(store)) = iter.next() {
							let (store_type, store_index) = (store >> 24, (store & 0x00FFFFFF) as usize);
							match store_type {
								0x00 => Expression::Variable {
									name: format!("local_data_{}", store_index),
									var_type: VariableType::Unknown,
								},
								0x7D => Expression::LocalVarRef(store_index),
								_ => panic!("Unexpected store for 0x53: {}", store)
							}
						} else {
							Expression::System(0x53)
						}
					} else {
						Expression::System(index as i32)
					}
				},
				0x7E => Expression::FunctionRef(index),
				0x7F => Expression::GlobalVarRef(index),
				_ => Expression::System(value as i32)
			}
		} else {
			return None;
		};

		while let Some(expr) = iter.next() {
			if let Expression::RawInt(-1) = expr {
				value = Expression::BinaryExpr {
					rhs: Box::new(iter.next().unwrap_or_else(|| {
						error!("No index for {}", value);
						Expression::Error
					})),
					lhs: Box::new(value), 
					op: BinaryOp::Index
				};
			} else {
				value = Expression::BinaryExpr {
					lhs: Box::new(value), 
					rhs: Box::new(expr),
					op: BinaryOp::Member
				};
			}
		}

		Some(value)
	}

	fn get_value(&mut self, var_type: VariableType) -> Expression {
		match var_type {
			VariableType::Int | VariableType::Str => self.pop(var_type),
			VariableType::IntRef | VariableType::StrRef =>
				if self.peek_type() == Some(var_type) {
					self.pop(var_type)
				} else {
					self.handle_frame().unwrap()
				},
			VariableType::IntList(_) | VariableType::StrList(_) => self.pop(var_type),

			VariableType::Void => panic!("Attempting to get a void!"),
			VariableType::Error => Expression::Error,
			VariableType::Unknown => self.pop(var_type),


			VariableType::Obj => {
				let value = self.pop(VariableType::Unknown);
				if value.get_type() == VariableType::Obj {
					value
				} else {
					// Assume it is integer and index of obj list
					if let Expression::RawInt(-1) = self.pop(VariableType::Int) {} else {
						panic!();
					}
					let list = self.get_value(VariableType::ObjList(0));
					Expression::BinaryExpr {
						lhs: Box::new(list),
						rhs: Box::new(value),
						op: BinaryOp::Index
					}
				}
			}
			VariableType::ObjList(_) => {
				let value = self.pop(VariableType::Unknown);
				if let VariableType::ObjList(_) = value.get_type() {
					value
				} else {
					// Assume it is integer and member of stage element
					let stage_elem = self.get_value(VariableType::StageElem);
					Expression::BinaryExpr {
						lhs: Box::new(stage_elem),
						rhs: Box::new(value),
						op: BinaryOp::Member
					}
				}
			},
			// TODO: handle stage_elem_list
			VariableType::StageElem => {
				if self.peek_type() == Some(VariableType::StageElem) {
					self.pop(VariableType::StageElem)
				} else {
					self.handle_frame().unwrap()
				}
			}
		}
	}
}


//
fn create_variable(value: Expression) -> (Expression, Instruction) {
	static mut NUM_VARS: usize = 0;

	let var_name = format!("var{}", unsafe {
		NUM_VARS += 1;
		NUM_VARS
	});

	let var = Expression::Variable {
		name: var_name,
		var_type: value.get_type()
	};

	let bind_inst = Instruction::Binding {
		lhs: var.clone(),
		rhs: value,
	};

	(var, bind_inst)
}

// TODO: this might not actually belong here - might be non system agnostic

// Checks if a function has an extra annoying (counter?) thing that makes the size
// of the instructions not known without looking at the stack
fn check_function_extra(function: &Expression) -> bool {
	if let &Expression::System(f) = function {
		if f == 0xc || f == 0x12 || f == 0x4c {
			true
		} else {
			false
		}
	} else {
		false
	}
}

////////////////////////////////////////////////////////////////////////////////

fn zip<A, B>(a: A, b: B) -> std::iter::Zip<<A as IntoIterator>::IntoIter, <B as IntoIterator>::IntoIter>
	where A: IntoIterator, B: IntoIterator
{
	a.into_iter().zip(b)
}

fn format_list<T: std::fmt::Display>(list: &[T]) -> String {
	let mut it = list.iter();
	if let Some(elem) = it.next() {
		let mut comma_separated = elem.to_string();

		for elem in it {
			comma_separated.push_str(", ");
			comma_separated.push_str(&elem.to_string());
		}
		comma_separated
	} else {
		String::new()
	}
}
