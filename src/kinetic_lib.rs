use std::fmt;

use ::{Variable, VariableType};
use ::Expression;
use ::expression::{FunctionType, BinaryOp};

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum KineticType {
	SheetList,
	Sheet,
	TableList,
	Table,		//SheetTable
	GroupList,
	Group,		//SheetGroup
	CellList,
	Cell,
	UiList,
	Ui,
	UnitList,
	Unit,

	IntKeyMapList,
	IntKeyMap,
	StrKeyMapList,
	StrKeyMap,

	JsonList,
	Json,

	IKMapKeyList,
	IKMapIndexList,
	SKMapKeyList,
	SKMapIndexList,
	KeyMapValue,

	Math,
	Touch,
	System,

	IntPointer,	// Int Event Pointer

	// TODO: these ones might not actually be Kinetic specific
	// At least, AB Siglus seems to use the same
	// Also, some of these aren't really types but it makes it so much simpler

	CounterList,
	Counter,

	SndBgmElem,
	SndPcmEsElem,
	SndPcmChList,


	Firebase
}

impl KineticType {
	fn to_var_type(self) -> VariableType {
		VariableType::Kinetic(self)
	}

	pub fn index_type(&self) -> VariableType {
		match *self {
			KineticType::SheetList     => KineticType::Sheet.to_var_type(),
			KineticType::TableList     => KineticType::Table.to_var_type(),
			KineticType::GroupList     => KineticType::Group.to_var_type(),
			KineticType::CellList      => KineticType::Cell.to_var_type(),
			KineticType::UiList        => KineticType::Ui.to_var_type(),
			KineticType::UnitList      => KineticType::Unit.to_var_type(),
			KineticType::CounterList   => KineticType::Counter.to_var_type(),
			KineticType::IntKeyMapList => KineticType::IntKeyMap.to_var_type(),
			KineticType::StrKeyMapList => KineticType::StrKeyMap.to_var_type(),
			KineticType::SndPcmChList  => KineticType::SndPcmEsElem.to_var_type(),
			KineticType::IKMapKeyList  => KineticType::KeyMapValue.to_var_type(),
			KineticType::SKMapKeyList  => KineticType::KeyMapValue.to_var_type(),
			KineticType::JsonList      => KineticType::Json.to_var_type(),
			_ => {
				warn!("Attempting to index type: {}", self);
				VariableType::Unknown
			}
		}
	}
}


impl fmt::Display for KineticType {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			KineticType::SheetList            => write!(f, "k_sheet[]"),
			KineticType::Sheet                => write!(f, "k_sheet"),
			KineticType::TableList            => write!(f, "k_table[]"),
			KineticType::Table                => write!(f, "k_table"),
			KineticType::GroupList            => write!(f, "k_group[]"),
			KineticType::Group                => write!(f, "k_group"),
			KineticType::CellList             => write!(f, "k_cell[]"),
			KineticType::Cell                 => write!(f, "k_cell"),
			KineticType::UiList               => write!(f, "k_ui[]"),
			KineticType::Ui                   => write!(f, "k_ui"),
			KineticType::UnitList             => write!(f, "k_unit[]"),
			KineticType::Unit                 => write!(f, "k_unit"),
			KineticType::CounterList          => write!(f, "k_counter[]"),
			KineticType::Counter              => write!(f, "k_counter"),
			KineticType::SndBgmElem           => write!(f, "k_snd_bgm_elem"),
			KineticType::SndPcmEsElem         => write!(f, "k_snd_pcmes_elem"),
			KineticType::SndPcmChList         => write!(f, "k_snd_pcmch_list"),
			KineticType::Touch                => write!(f, "k_touch"),
			KineticType::Math                 => write!(f, "k_math"),
			KineticType::System               => write!(f, "k_sys"),
			KineticType::IntPointer           => write!(f, "k_int_eve_pointer"),
			KineticType::IntKeyMapList        => write!(f, "k_ikmap[]"),
			KineticType::IntKeyMap            => write!(f, "k_ikmap"),
			KineticType::StrKeyMapList        => write!(f, "k_skmap[]"),
			KineticType::StrKeyMap            => write!(f, "k_skmap"),
			KineticType::JsonList             => write!(f, "k_json[]"),
			KineticType::Json                 => write!(f, "k_json"),
			KineticType::IKMapKeyList         => write!(f, "k_ikmap_keylist"),
			KineticType::IKMapIndexList       => write!(f, "k_ikmap_indexlist"),
			KineticType::SKMapKeyList         => write!(f, "k_skmap_keylist"),
			KineticType::SKMapIndexList       => write!(f, "k_skmap_indexlist"),
			KineticType::KeyMapValue          => write!(f, "k_keymapvalue"),
			KineticType::Firebase             => write!(f, "k_firebase"),
		}
	}
}

pub fn replace(expr: &mut Expression) {
	match *expr {
		Expression::System(index) => replace_sys(expr, index),
		Expression::BinaryExpr { ref mut lhs, ref mut rhs, op } => {
			if op == BinaryOp::Member {
				replace_member(lhs, rhs);
			}
		},
		_ => {}
	}
}

fn replace_sys(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = var_expr("g_sheets", KineticType::SheetList),
		0x01000002 => *expr = var_expr("g_touch", KineticType::Touch),
		0x01000008 => *expr = var_expr("g_ikmaps", KineticType::IntKeyMapList),
		0x01000009 => *expr = var_expr("g_skmaps", KineticType::StrKeyMapList),
		0x0100000a => *expr = named_func("g_savedata_save"),
		0x01000019 => *expr = var_expr("g_json_list", KineticType::JsonList),
		0x27 => *expr = var_expr("g_math", KineticType::Math),
		0x28 => *expr = var_expr("g_counters", KineticType::CounterList),
		0x2A => *expr = var_expr("g_sndbgm_element", KineticType::SndBgmElem),
		0x2B => *expr = var_expr("g_sndpcmes_element", KineticType::SndPcmEsElem),
		0x2C => *expr = var_expr("g_sndpcmch_list", KineticType::SndPcmChList),
		0x5C => *expr = var_expr("g_system", KineticType::System),	// the real system is here
		0x8D => *expr = named_func("init_call_stack"),
		0x92 => *expr = named_func("file_exists"),
		0xA4 => *expr = var_expr("g_firebase", KineticType::Firebase),
		_ => warn!("Unrecognised global field: {:#x}", index)
	}
}

fn replace_member(lhs: &mut Expression, rhs: &mut Expression) {
	if let Expression::RawInt(index) = *rhs {
		let var_type = lhs.get_type();
		match var_type {
			VariableType::Kinetic(kin_type) => {
				match kin_type {
					KineticType::Sheet => replace_sheet(rhs, index),
					KineticType::Table => replace_table(rhs, index),
					KineticType::Group => replace_group(rhs, index),
					KineticType::Cell => replace_cell(rhs, index),
					KineticType::Ui => replace_ui(rhs, index),
					KineticType::Unit => replace_unit(rhs, index),
					KineticType::Counter => replace_counter(rhs, index),
					KineticType::SndBgmElem => replace_bgm_elem(rhs, index),
					KineticType::SndPcmEsElem => replace_pcmes_elem(rhs, index),
					KineticType::Touch => replace_touch(rhs, index),
					KineticType::IntPointer => replace_int_event_pointer(rhs, index),
					KineticType::IntKeyMap => replace_ikmap(rhs, index),
					KineticType::StrKeyMap => replace_skmap(rhs, index),
					KineticType::Json => replace_json(rhs, index),
					KineticType::KeyMapValue => replace_keymapvalue(rhs, index),
					KineticType::Math => replace_math(rhs, index),
					KineticType::Firebase => replace_firebase(rhs, index),
					KineticType::System => replace_system(rhs, index),
					_ => warn!("Unrecognised types: {} -> {}", lhs, rhs)
				}
			},
			VariableType::IntList(_) => replace_int_list(rhs, index),
			VariableType::StrList(_) => replace_str_list(rhs, index),
			_ => {}
		}
	} else {
		warn!("Unrecognised rhs type: {} -> {}", lhs, rhs);
	}
}

// Specific for types
fn replace_int_list(expr: &mut Expression, index: i32) {
	match index {
		0x02 => *expr = named_func("resize"),
		0x09 => *expr = named_func("length"),
		0x0a => *expr = named_func("reset"),
		0x0100000B => *expr = named_func("push"),
		_ => warn!("Unrecognised int list field {:#x}", index)
	}
}

fn replace_str_list(expr: &mut Expression, index: i32) {
	match index {
		0x02 => *expr = named_func("resize"),
		0x03 => *expr = named_func("reset"),
		0x04 => *expr = named_func("length"),
		0x01000002 => *expr = named_func("push"),
		_ => warn!("Unrecognised str list field {:#x}", index)
	}
}


// Display
fn replace_sheet(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = var_expr("tables", KineticType::TableList),
		_ => warn!("Unrecognised sheet field {:#x}", index)
	}
}

fn replace_table(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = var_expr("groups", KineticType::GroupList),
		0x01000001 => *expr = named_func("create"),
		_ => warn!("Unrecognised table field {:#x}", index)
	}
}

fn replace_group(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = var_expr("cells", KineticType::CellList),
		0x01000001 => *expr = named_func("create"),
		0x01000002 => *expr = named_func("delete"),
		0x01000003 => *expr = named_func("exists"),
		//0x01000005 => *expr = named_func("on_off"),	// anime_type
		0x0100000A => *expr = var_expr("dp_pos_x_event_pointer", KineticType::IntPointer),
		0x0100000B => *expr = var_expr("dp_pos_y_event_pointer", KineticType::IntPointer),
		0x0100000C => *expr = var_expr("dp_tr_event_pointer", KineticType::IntPointer),
		0x0100000D => *expr = named_func("set_free_pos_enable"),
		0x0100000E => *expr = named_func("set_base_clip_rect"),
		0x0100000F => *expr = named_func("set_base_clip_x1x2"),
		0x01000010 => *expr = named_func("set_base_clip_y1y2"),
		0x01000011 => *expr = named_func("set_base_clip_x1"),
		0x01000012 => *expr = named_func("set_base_clip_x2"),
		0x01000013 => *expr = named_func("set_base_clip_y1"),
		0x01000014 => *expr = named_func("set_base_clip_y2"),
	
		0x0 => *expr = named_func("delete_cells"),
		_ => warn!("Unrecognised group field {:#x}", index)
	}
}

fn replace_cell(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = var_expr("uis", KineticType::UiList),
		0x01000001 => *expr = named_func("create"),
		0x0100000F => *expr = named_func("set_select_state"),	// scale, fog-bright
		0x01000011 => *expr = named_func("set_se"),
		0x01000012 => *expr = named_func("exists"),
		0x01000016 => *expr = int_var_expr("dp_pos_x"),
		0x01000017 => *expr = int_var_expr("dp_pos_y"),
		0x01000018 => *expr = int_var_expr("dp_tr"),
		0x01000019 => *expr = var_expr("dp_pos_x_event_pointer", KineticType::IntPointer),
		0x0100001B => *expr = var_expr("dp_tr_event_pointer", KineticType::IntPointer),
		0x0100002A => *expr = named_func("set_fixed_width"),
		0x01000031 => *expr = int_var_expr("btn_id_pointer"),
		0x01000033 => *expr = named_func("set_own_clip_rect"),
		0x01000034 => *expr = named_func("set_own_clip_x1x2"),
		0x01000035 => *expr = named_func("set_own_clip_y1y2"),
		0x01000036 => *expr = named_func("set_own_clip_x1"),
		0x01000037 => *expr = named_func("set_own_clip_x2"),
		0x01000038 => *expr = named_func("set_own_clip_y1"),
		0x01000039 => *expr = named_func("set_own_clip_y2"),

		0x00 => *expr = int_var_expr("canvas_scale_x"),
		0x01 => *expr = int_var_expr("canvas_scale_y"),
		0x02 => *expr = int_var_expr("canvas_dp_center_rep_x"),
		0x03 => *expr = int_var_expr("canvas_dp_center_rep_y"),
		0x04 => *expr = var_expr("canvas_dp_center_rep_x_event_pointer", KineticType::IntPointer),
		0x05 => *expr = var_expr("canvas_dp_center_rep_y_event_pointer", KineticType::IntPointer),
		0x15 => *expr = named_func("set_canvas_height"),
		_ => warn!("Unrecognised cell field {:#x}", index)
	}
}

fn replace_ui(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = named_func("create_image"),
		0x01000005 => *expr = named_func("create_string"),
		0x01000006 => *expr = named_func("set_string_moji_size"),
		0x01000007 => *expr = named_func("set_string_param"),

		0x01000025 => *expr = named_func("set_select_state"),	// alpha, bright, dark, scale, fog_bright
		0x01000030 => *expr = named_func("set_string"),
		0x01000031 => *expr = named_func("set_waku_color_0"),
		0x01000032 => *expr = named_func("set_waku_color_1"),
		0x01000033 => *expr = named_func("set_waku_color_2"),
		0x01000034 => *expr = named_func("set_waku_color_3"),
		0x01000035 => *expr = named_func("set_moji_decoration_normal"),
		0x01000036 => *expr = named_func("set_moji_decoration_hit"),
		0x01000037 => *expr = named_func("set_moji_decoration_select"),
		0x01000038 => *expr = named_func("set_moji_decoration_not"),

		0x01000043 => *expr = var_expr("scale_alignment_x_event_pointer", KineticType::IntPointer),
		0x01000044 => *expr = var_expr("scale_alignment_y_event_pointer", KineticType::IntPointer),
		0x01000045 => *expr = int_var_expr("scale_alignment_x"),
		0x01000046 => *expr = int_var_expr("scale_alignment_y"),

		0x01000048 => *expr = int_var_expr("dp_priority_layer"),
		0x0100004A => *expr = named_func("create_waku"),
		0x0100004B => *expr = int_var_expr("dp_tr<to check!>"),
		0x0100004C => *expr = int_var_expr("dp_scale_x"),
		0x0100004D => *expr = int_var_expr("dp_scale_y"),
		0x0100004E => *expr = int_var_expr("dp_rotate_z"),
		0x0100004F => *expr = var_expr("dp_tr_event_pointer", KineticType::IntPointer),
		0x01000050 => *expr = var_expr("dp_scale_x_event_pointer", KineticType::IntPointer),
		0x01000051 => *expr = var_expr("dp_scale_y_event_pointer", KineticType::IntPointer),
		0x01000052 => *expr = var_expr("dp_scale_y_event_pointer", KineticType::IntPointer),
		0x01000053 => *expr = int_var_expr("dp_center_rep_x"),
		0x01000054 => *expr = int_var_expr("dp_center_rep_y"),

		0x01000057 => *expr = int_var_expr("dp_center_pos_x"),
		0x01000058 => *expr = int_var_expr("dp_center_pos_y"),
	
		0x01000066 => *expr = int_var_expr("dp_dark"),
		0x01000069 => *expr = var_expr("dp_dark_event_pointer", KineticType::IntPointer),

		0x0100006D => *expr = named_func("set_se"),
		0x0100006E => *expr = named_func("exists"),

		0x01000077 => *expr = int_var_expr("dp_disp"),
		0x0100007D => *expr = int_var_expr("btn_id"),
		0x010000AB => *expr = var_expr("units", KineticType::UnitList),

		0x00 => *expr = int_var_expr("dp_color_r"),
		0x01 => *expr = int_var_expr("dp_color_g"),
		0x02 => *expr = int_var_expr("dp_color_b"),
		0x07 => *expr = var_expr("dp_fog_bright_event_pointer", KineticType::IntPointer),
		_ => warn!("Unrecognised ui field {:#x}", index)
	}
}

fn replace_unit(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = named_func("exists"),
		0x01000001 => *expr = named_func("create"),
		0x01000002 => *expr = named_func("delete"),
		0x01000003 => *expr = int_var_expr("dp_disp"),
		0x01000004 => *expr = int_var_expr("dp_pat_no"),
		0x01000005 => *expr = int_var_expr("dp_pos_x"),
		0x01000006 => *expr = int_var_expr("dp_pos_y"),
		0x01000007 => *expr = int_var_expr("dp_tr"),
		0x01000008 => *expr = var_expr("dp_pat_no_event_ptr", KineticType::IntPointer),
		0x01000009 => *expr = var_expr("dp_pos_x_event_ptr", KineticType::IntPointer),
		0x0100000A => *expr = var_expr("dp_pos_y_event_ptr", KineticType::IntPointer),
		0x0100000B => *expr = var_expr("dp_tr_event_ptr", KineticType::IntPointer),
		0x0100000C => *expr = named_func("init_param"),
		0x0100000D => *expr = named_func("set_param"),
		0x0100000E => *expr = named_func("set_pos"),
		0x01000014 => *expr = int_var_expr("dp_priority_order"),
		0x0100003C => *expr = var_expr("dp_priority_order_event_ptr", KineticType::IntPointer),
		_ => warn!("Unrecognised unit field {:#x}", index)
	}
}

// System
fn replace_counter(expr: &mut Expression, index: i32) {
	match index {
		0x00 => *expr = named_func("set_count"),
		0x01 => *expr = named_func("get_count"),
		0x02 => *expr = named_func("reset"),
		0x03 => *expr = named_func("start_counter<false>"),
		0x04 => *expr = named_func("stop"),
		0x05 => *expr = named_func("resume"),
		0x06 => *expr = named_func("wait<false>"),
		0x07 => *expr = named_func("check"),	//checks >= XXX
		0x08 => *expr = named_func("wait<true>"),
		0x09 => *expr = named_func("start_counter<true>"),
		_ => warn!("Unrecognised counter field {:#x}", index)
	}
}

fn replace_bgm_elem(expr: &mut Expression, index: i32) {
	match index {
		0x00 => *expr = named_func("play"),
		_ => warn!("Unrecognised bgm elem field {:#x}", index)
	}
}

fn replace_pcmes_elem(_expr: &mut Expression, index: i32) {
	match index {
		_ => warn!("Unrecognised pcmes elem field {:#x}", index)
	}
}


fn replace_int_event_pointer(expr: &mut Expression, index: i32) {
	match index {
		0x0100000c => *expr = named_func("add_timetable"),
		_ => warn!("Unrecognised int eve pointer field {:#x}", index)
	}
}

fn replace_ikmap(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = named_func("free"),
		0x01000001 => *expr = named_func("add"),
		0x01000004 => *expr = named_func("key_exists"),
		0x01000005 => *expr = named_func("index_exists"),
		//0x01000006 => *expr = named_func("get_key_for_index"),
		0x01000007 => *expr = var_expr("keys", KineticType::IKMapKeyList),
		0x01000008 => *expr = var_expr("indices", KineticType::IKMapIndexList),
		//0x01000009 => length

		//0x00 => sort		
		//0x01 => add and get pointer?	
		_ => warn!("Unrecognised int key map field {:#x}", index)
	}
}

fn replace_skmap(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = named_func("free"),
		0x01000001 => *expr = named_func("add"),
		0x01000002 => *expr = named_func("del_for_key"),
		0x01000003 => *expr = named_func("del_for_index"),
		0x01000004 => *expr = named_func("key_exists"),
		0x01000005 => *expr = named_func("index_exists"),
		//0x01000006 => *expr = named_func("get_key_for_index"),
		0x01000007 => *expr = var_expr("keys", KineticType::SKMapKeyList),
		0x01000008 => *expr = var_expr("indices", KineticType::SKMapIndexList),
		//0x01000009 => length
		0x0100000A => *expr = named_func("sort"),
		_ => warn!("Unrecognised str key map field {:#x}", index)
	}
}

fn replace_json(expr: &mut Expression, index: i32) {
	match index {
		0x0100000C => *expr = named_func("exists"),
		0x0100000F => *expr = named_func("length"),
		0x01000010 => *expr = named_func("get_int"),

		_ => warn!("Unrecognised json field {:#x}", index)
	}
}

fn replace_keymapvalue(expr: &mut Expression, index: i32) {
	match index {
		0x01000000 => *expr = int_var_expr("value"),
		_ => warn!("Unrecognised key map value field {:#x}", index)
	}
}

// Special 
fn replace_touch(_expr: &mut Expression, index: i32) {
	match index {
		_ => warn!("Unrecognised touch field {:#x}", index)
	}
}

fn replace_math(expr: &mut Expression, index: i32) {
	match index {
		0x00 => *expr = named_func("randint"),	// Inclusive integer in [a, b], implementation is with a modulo
		0x01 => *expr = named_func("to_string"),
		0x03 => *expr = named_func("max"),
		0x04 => *expr = named_func("min"),
		0x05 => *expr = named_func("abs"),
		0x06 => *expr = named_func("sine"),		// sine(a, b) = a * sine(10 * rad(b))
		0x07 => *expr = named_func("cosine"),
		0x09 => *expr = named_func("lerp"),
		0x0a => *expr = named_func("clamp"),
		0x0e => *expr = named_func("sqrt_mult"), // sqrt_mult(a, b) = sqrt(a) * b
		0x14 => *expr = named_func("logarithm"), // logarithm is base 2 with constant mult
		0x16 => *expr = named_func("get_angle"),
		_ => warn!("Unrecognised math function {:#x}", index)
	}
}

fn replace_system(expr: &mut Expression, index: i32) {
	match index {
		0x01000001 => *expr = named_func("get_date_info"),
		0x01000002 => *expr = named_func("get_unix_time"),
		_ => warn!("Unrecognised system function {:#x}", index)
	}
}

fn replace_firebase(expr: &mut Expression, index: i32) {
	match index {
		0x00 => *expr = named_func("set_user_property"),
		0x01 => *expr = named_func("add_int_value"),
		0x02 => *expr = named_func("add_string_value"),
		0x03 => *expr = named_func("log_event"),
		0x04 => *expr = named_func("init_event"),
		0x05 => *expr = named_func("subscribe_topic"),
		0x06 => *expr = named_func("unsubscribe_topic"),
		_ => warn!("Unrecognised firebase function {:#x}", index)
	}
}


// Helpers
fn int_var_expr(name: &str) -> Expression {
	Variable {
		name: name.to_string(),
		var_type: VariableType::Int
	}.to_expression()
}

fn var_expr(name: &str, k_type: KineticType) -> Expression {
	Variable {
		name: name.to_string(),
		var_type: k_type.to_var_type()
	}.to_expression()
}

fn named_func(name: &str) -> Expression {
	let func = FunctionType::Named(name.to_string());
	Expression::Function(func)
}