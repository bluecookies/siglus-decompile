use std;

use ::VariableType;
use ::cfg::Instruction;

////////////////////////////////////////////////////////////////////////////////
#[derive(Clone, Debug)]
pub enum Expression {
	RawInt(i32),
	RawString(String),
	Variable { name: String, var_type: VariableType },

	UnaryExpr {
		value: Box<Expression>,
		op: UnaryOp
	},

	BinaryExpr {
		lhs: Box<Expression>,
		rhs: Box<Expression>,
		op: BinaryOp
	},
	Function(FunctionType),
	FunctionCall { 
		function: Box<Expression>, 
		option: u32, 
		args: Vec<Expression>, 
		extra_params: Vec<u32>, 
		return_type: VariableType, 
		extra: Option<u32>
	},
	System(i32),
	Error
}

#[derive(Clone, Debug)]
pub enum FunctionType {
	//System(i32),
	Procedure(usize),
	Named(String),
}

impl Expression {
	pub fn procedure_call(label: usize, args: Vec<Expression>) -> Expression {
		let function = FunctionType::Procedure(label);
		Expression::FunctionCall {
			function: Box::new(Expression::Function(function)), 
			option: 0, 
			args, 
			extra_params: Vec::new(), 
			return_type:
			VariableType::Unknown, 
			extra: None
		}
	}
}

impl Expression {
	pub fn has_side_effect(&self) -> bool {
		match *self {
			Expression::RawInt(_) => false,
			Expression::RawString(_) => false,
			Expression::Variable { .. } => false,
			Expression::UnaryExpr { ref value, .. } => value.has_side_effect(),
			Expression::BinaryExpr { ref lhs, ref rhs, .. } => lhs.has_side_effect() || rhs.has_side_effect(),
			Expression::Function(_) => panic!("Function being checked! Check it out."),
			Expression::FunctionCall { .. } => true,
			Expression::System(_) => false,
			Expression::Error => true
		}
	}

	pub fn to_inst(self) -> Instruction {
		Instruction::Expression(self)
	}

	pub fn get_type(&self) -> VariableType {
		match *self {
			Expression::RawInt(_) => VariableType::Int,
			Expression::RawString(_) => VariableType::Str,
			Expression::Variable { var_type, .. } => var_type,
			Expression::UnaryExpr { ref value, .. } => value.get_type(),	// temp
			Expression::BinaryExpr { ref lhs, op, .. } => {
				match op {
					BinaryOp::Index => match lhs.get_type() {
						VariableType::IntList(_) => VariableType::Int,
						VariableType::StrList(_) => VariableType::Str,
						VariableType::ObjList(_) => VariableType::Obj,
						_ => {
							//warn!("Indexing a list: {}", self);
							VariableType::Unknown
						}
					}
					BinaryOp::Eq | BinaryOp::Neq | BinaryOp::And | BinaryOp::Or => VariableType::Int,
					_ => lhs.get_type()
				}
			},
			Expression::Function(_) => panic!(),
			Expression::FunctionCall { return_type, .. } => return_type,
			Expression::System(_) => VariableType::Unknown,
			Expression::Error => VariableType::Error,
		}
	}

	pub fn calc1(value: Expression, op: u8) -> Expression {
		let op = match op {
			0x01 => return value,
			0x02 => UnaryOp::Negate,
			0x30 => UnaryOp::BitwiseNot,
			_    => {
				error!("Unknown unary operation: {:#02x}", op);
				return Expression::Error
			}
		};

		Expression::UnaryExpr {
			value: Box::new(value), op
		}
	}

	pub fn calc2_int(lhs: Expression, rhs: Expression, op: u8) -> Expression {
		let op = match op {
			0x01 => BinaryOp::Add,
			0x02 => BinaryOp::Sub,
			0x03 => BinaryOp::Mul,
			0x04 => BinaryOp::Div,
			0x05 => BinaryOp::Rem,
			0x10 => BinaryOp::Neq,
			0x11 => BinaryOp::Eq,
			0x12 => BinaryOp::Leq,
			0x13 => BinaryOp::Lt,
			0x14 => BinaryOp::Geq,
			0x15 => BinaryOp::Gt,
			0x20 => BinaryOp::And,
			0x21 => BinaryOp::Or,
			_    => {
				error!("Unknown integer binary operation: {:#02x}", op);
				return Expression::Error
			}
		};

		Expression::BinaryExpr {
			lhs: Box::new(lhs), 
			rhs: Box::new(rhs),
			op
		}
	}

	pub fn calc2_str(lhs: Expression, rhs: Expression, op: u8) -> Expression {
		let op = match op {
			0x01 => BinaryOp::Add,
			0x11 => BinaryOp::Eq,
			_    => {
				error!("Unknown string binary operation: {:#02x}", op);
				return Expression::Error
			}
		};

		Expression::BinaryExpr {
			lhs: Box::new(lhs), 
			rhs: Box::new(rhs),
			op
		}
	}

	// TODO: check if it is already a negate
	// TODO: also delegate if it is a boolean and/or
	pub fn negate(self) -> Expression {
		match self {
			Expression::RawInt(num) => Expression::RawInt(if num == 0 { 1 } else { 0 }),
			Expression::RawString(string) => panic!("Tried to negate {}", string),
			Expression::UnaryExpr{value, op: UnaryOp::BooleanNot} => *value,
			Expression::BinaryExpr{lhs, rhs, op} => {
				match op {
					BinaryOp::Eq => Expression::BinaryExpr{lhs, rhs, op: BinaryOp::Neq},
					BinaryOp::Neq => Expression::BinaryExpr{lhs, rhs, op: BinaryOp::Eq},
					BinaryOp::Gt => Expression::BinaryExpr{lhs, rhs, op: BinaryOp::Leq},
					BinaryOp::Geq => Expression::BinaryExpr{lhs, rhs, op: BinaryOp::Lt},
					BinaryOp::Lt => Expression::BinaryExpr{lhs, rhs, op: BinaryOp::Geq},
					BinaryOp::Leq => Expression::BinaryExpr{lhs, rhs, op: BinaryOp::Gt},
					_ => {
						Expression::UnaryExpr {
						value: Box::new(Expression::BinaryExpr{lhs, rhs, op}),
						op: UnaryOp::BooleanNot
						}
					}
				}
			}
			_ => {
				Expression::UnaryExpr {
					value: Box::new(self),
					op: UnaryOp::BooleanNot
				}
			}	
		}
	}

	fn precedence(&self) -> u8 {
		match *self {
			Expression::UnaryExpr{..} => 11,
			Expression::BinaryExpr{op, ..} => {
				match op {
					BinaryOp::Add => 9,
					BinaryOp::Sub => 9,
					BinaryOp::Eq => 6,
					BinaryOp::Neq => 6,
					BinaryOp::Index => 11,
					BinaryOp::Member => 11,
					BinaryOp::Mul => 10,
					BinaryOp::Div => 10,
					BinaryOp::Rem => 10,
					BinaryOp::Gt => 7,
					BinaryOp::Geq => 7,
					BinaryOp::Lt => 7,
					BinaryOp::Leq => 7,
					BinaryOp::And => 2,
					BinaryOp::Or => 1,
				}
			},
			_ => 0xFF
		}
	}
}

// TODO: member actually has higher precedence than index, but similar to subtraction
//	Precedence table
//    [-] [~] [!] (Unary) [] (Index) -> (Member)
//    * / %
//    + -
//    << >> >>>
//    < <= > >=
//    == !=
//    &
//    ^
//    |
//    &&
//    ||


impl std::fmt::Display for Expression {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Expression::RawInt(num) => write!(f, "{}", num),
			Expression::RawString(ref string) => write!(f, "\"{}\"", string),
			Expression::Variable{ref name, .. } => write!(f, "{}", name),
			Expression::UnaryExpr{ref value, op} => {
				if self.precedence() > value.precedence() {
					write!(f, "{}({})", op, value)
				} else {
					write!(f, "{}{}", op, value)
				}
			},
			Expression::BinaryExpr{ref lhs, ref rhs, op} => {
				let precedence = self.precedence();

				let left_expr = if precedence > lhs.precedence() {
					format!("({})", lhs)
				} else {
					format!("{}", lhs)
				};

				if op == BinaryOp::Index {
					write!(f, "{}[{}]", left_expr, rhs)
				} else {
					let right_precedence = rhs.precedence();
					let right_expr = if precedence > right_precedence {
						format!("({})", rhs)
					} else if precedence < right_precedence {
						format!("{}", rhs)
					} else {
						// Non associative
						if op == BinaryOp::Sub || op == BinaryOp::Div || op == BinaryOp::Member {
							format!("({})", rhs)
						} else {
							format!("{}", rhs)
						}
					};
					write!(f, "{}{}{}", left_expr, op, right_expr)
				}
			},
			Expression::Function(ref func_type) => write!(f, "{}", func_type),
			Expression::FunctionCall {
				ref function, option, ref args, ref extra_params, extra, ..
			} => {
				let option_str = if option == 0 { String::new() } else { format!("{{{}}}", option) };
				let extra_param_str = if extra_params.is_empty() { String::new() } else { format!("<{}>", format_list(extra_params)) };
				let extra_str = if let Some(extra) = extra { format!(", {}", extra) } else { String::new() };
				write!(f, "{}{}({}){}{}", function, option_str, format_list(args), extra_param_str, extra_str)
			},
			Expression::System(num) => write!(f, "sys_{:#x}", num),
			Expression::Error => write!(f, "ERROR")
		}
	}
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum BinaryOp {
	Add,
	Sub,
	Mul,
	Div,
	Rem,
	Eq,
	Neq,
	Gt,
	Geq,
	Lt,
	Leq,

	And,
	Or,

	Index,
	Member,
}


impl std::fmt::Display for BinaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			BinaryOp::Add => write!(f, " + "),
			BinaryOp::Sub => write!(f, " - "),
			BinaryOp::Mul => write!(f, " * "),
			BinaryOp::Div => write!(f, " / "),
			BinaryOp::Rem => write!(f, " % "),
			BinaryOp::Eq => write!(f, " == "),
			BinaryOp::Neq => write!(f, " != "),
			BinaryOp::Gt => write!(f, " > "),
			BinaryOp::Geq => write!(f, " >= "),
			BinaryOp::Lt => write!(f, " < "),
			BinaryOp::Leq => write!(f, " <= "),
			BinaryOp::And => write!(f, " && "),
			BinaryOp::Or => write!(f, " || "),
			BinaryOp::Index => write!(f, "[]"),
			BinaryOp::Member => write!(f, "."),
		}
	}
}


#[derive(Copy, Clone, Debug)]
pub enum UnaryOp {
	// Identity,
	Negate,
	BitwiseNot,
	BooleanNot,
}

impl std::fmt::Display for UnaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			UnaryOp::Negate => write!(f, "-"),
			UnaryOp::BitwiseNot => write!(f, "~"),
			UnaryOp::BooleanNot => write!(f, "!"),
		}
	}
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


impl std::fmt::Display for FunctionType {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			FunctionType::Procedure(num) => write!(f, "PROC_{:#x}", num),
			FunctionType::Named(ref name) => write!(f, "{}", name),
		}
	}
}