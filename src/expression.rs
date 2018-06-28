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

	Function(String),
	FunctionCall { 
		function: Box<Expression>, 
		option: u32, 
		args: Vec<Expression>, 
		extra_params: Vec<u32>, 
		return_type: VariableType, 
		extra: Option<u32>
	},
	Error
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
			0x12 => BinaryOp::Gt,
			0x13 => BinaryOp::Geq,
			0x14 => BinaryOp::Lt,
			0x15 => BinaryOp::Leq,
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
}

impl std::fmt::Display for Expression {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Expression::RawInt(num) => write!(f, "{}", num),
			Expression::RawString(ref string) => write!(f, "{}", string),
			Expression::Variable{ref name, .. } => write!(f, "{}", name),
			Expression::UnaryExpr{ref value, op} => write!(f, "({} {})", op, value),
			// TODO: treat these with precedences
			Expression::BinaryExpr{ref lhs, ref rhs, op} => {
				if op == BinaryOp::Index {
					write!(f, "({})[{}]", lhs, rhs)
				} else {
					write!(f, "({}){}({})", lhs, op, rhs)
				}
			},
			Expression::Function(ref string) => write!(f, "{}", string),
			Expression::FunctionCall {
				ref function, option, ref args, ref extra_params, return_type: _return_type, extra
			} => write!(f, "{}<{}>({:?})<{:?}>, {:?}", function, option, args, extra_params, extra),
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
}

impl std::fmt::Display for UnaryOp {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			UnaryOp::Negate => write!(f, " - "),
			UnaryOp::BitwiseNot => write!(f, " ~ "),
		}
	}
}
