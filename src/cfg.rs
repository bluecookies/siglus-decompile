// TODO: clean up the loop detection and structuring code
// TODO: find all the TODOs and fix
// TODO: remove the panics
// TODO: make the gotos more robust - have an actual labelling system
//	 TODO: this includes the stupid ass current line system with statements right now
//	 TODO: seriously, even a solution involving assigning a unique id to each statement that begins a block
//			linking gotos to that unique id
//			and checking if it is linked to and adding the label when writing would be a better solution
//	 TODO: ^ do that, at least its better than this crap
// TODO: do some tests

use std;
use std::io::Write;

use std::collections::{HashSet, HashMap};

use petgraph::Direction;
use petgraph::graph::{Graph, NodeIndex};
use petgraph::visit::{IntoNodeReferences, DfsPostOrder, Walker};
use petgraph::algo::{dominators::{simple_fast as find_dominators}, is_isomorphic};
use petgraph::dot::{Dot, Config as DotCfg};

use ::Result;
use ::Expression;

use ::Variable;
use ::Function;
use ::format_list;

// Note: petgraph NodeIndices must not be used after a node is removed
pub struct ControlFlowGraph {
	graph: Graph<Block, GraphEdge>,
	entry: NodeIndex,
	is_function: bool,

	if_follow: HashMap<NodeIndex, NodeIndex>,
	loop_head: HashMap<NodeIndex, NodeIndex>,
	loop_latch: HashMap<NodeIndex, NodeIndex>,

	loops: Vec<Loop>,

	post_order: Vec<NodeIndex>
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum GraphEdge {
	Entry(usize),
	TwoWay(bool),
	OneWay,
}

impl ControlFlowGraph {
	pub fn main(entrypoints: &[(usize, usize)]) -> Self {
		let mut graph = Graph::new();
		let head = graph.add_node(Block::new(std::usize::MAX));	// TODO: temp, remove
		for &(z_level, entry_address) in entrypoints {
			let succ = graph.add_node(Block::new(entry_address));
			graph.update_edge(head, succ, GraphEdge::Entry(z_level));
		}
		ControlFlowGraph {
			graph,
			entry: head,
			is_function: false,

			if_follow: HashMap::new(),
			loop_head: HashMap::new(),
			loop_latch: HashMap::new(),

			loops: Vec::new(),

			post_order: Vec::new(),
		}
		
	}
	pub fn function(address: usize) -> Self {
		let mut graph = Graph::new();
		let head = graph.add_node(Block::new(address));
		ControlFlowGraph {
			graph,
			entry: head,
			is_function: true,

			if_follow: HashMap::new(),
			loop_head: HashMap::new(),
			loop_latch: HashMap::new(),

			loops: Vec::new(),

			post_order: Vec::new(),
		}
	}

	pub fn get_block_id_at(&mut self, address: usize) -> NodeIndex {
		if let Some((index, ref _block)) = self.graph
			.node_references()
			.find(|&(_index, ref block)| {
				block.address == address
			}
		) { // find_map
			return index;
		}
		self.graph.add_node(Block::new(address))
	}

	pub fn traversed(&self, index: NodeIndex) -> bool {
		self.graph[index].traversed
	}

	pub fn set_traversed(&mut self, index: NodeIndex) {
		self.graph[index].traversed = true;
	}

	pub fn add_inst(&mut self, block_id: NodeIndex, inst: Instruction) {
		self.graph[block_id].add_inst(inst);
	}

	pub fn add_successor(&mut self, pred: NodeIndex, succ: NodeIndex) {
		self.graph.update_edge(pred, succ, GraphEdge::OneWay);
	}

	pub fn add_branch(&mut self, block_id: NodeIndex, condition: Expression, then_block: NodeIndex, else_block: NodeIndex) {
		self.graph[block_id].condition = Some(condition);

		self.graph.update_edge(block_id, then_block, GraphEdge::TwoWay(true));
		self.graph.update_edge(block_id, else_block, GraphEdge::TwoWay(false));
	}

	fn get_then_else(&self, block_id: NodeIndex) -> Result<(NodeIndex, NodeIndex)> {
		let mut succ = self.graph.neighbors(block_id).detach();

		// Edge to true block is labelled with Some(true)
		let (edge_index, node_index) = succ.next(&self.graph).ok_or("")?;
		let edge_weight = self.graph.edge_weight(edge_index).ok_or("")?;
		if edge_weight == &GraphEdge::TwoWay(true) {
			// node_index is the true block, and the next one is false block
			Ok((node_index, succ.next(&self.graph).ok_or("")?.1))
		} else if edge_weight == &GraphEdge::TwoWay(false) {
			Ok((succ.next(&self.graph).ok_or("")?.1, node_index))
		} else {
			Err("Not a valid 2-way".into())
		}
	}
}

// Structuring
impl ControlFlowGraph {
	pub fn structure_statements(&mut self) -> Vec<Statement> {
		trace!("Starting graph structuring...");

		self.structure_loops();

		self.structure_ifs();

		// Construct the actual statements
		let mut constructor = StatementConstructor::new();
		let mut statements = constructor.construct_statements(self, self.entry);
		simplify_statements(&mut statements, &constructor);

		statements
	}


	// Determine follow nodes for 2-way conditional nodes
	// This step must be done after loops are found or weirdness will ensue
	fn structure_ifs(&mut self) {
		trace!("Structuring 2-ways...");
		let dominators = find_dominators(&self.graph, self.entry);

		let mut unresolved: HashSet<NodeIndex> = HashSet::new();

		// For each 2-way node that is not part of the header or latching node of a loop, 
		// the follow node is calculated as the node that takes it as an immediate dominator 
		// and has two or more in-edges (since it must be reached by at least two different paths from the header). 

		// If there is more than one such node, the one that encloses the maximum number of nodes is selected 
		// (i.e. the one with the largest number). 
		
		// If such a node is not found, the 2-way header node is placed on the unresolved set. 
		// Whenever a follow node is found, all nodes that belong to the set of unresolved nodes 
		// are set to have the same follow node as the one just found 
		// (i.e. they are nested conditionals or unstructured conditionals that reach this node).
		for node in self.post_order() {
			// Check if it is a 2-way that is not a head or latching node
			// ALSO structure n-ways at the same time
			if self.graph.edges(node).count() >= 2 && !self.is_head_latch(node) {
				// Find the maximum node (in RPO) such that it
				//	* has more than two predecessors
				//	* is immediately dominated by `node`
				// if it exists.
				// This is equivalent to finding the first node in a post-ordering.
				//	i think

				let mut post_order = self.post_order().into_iter();

				// TODO: only need to check the nodes up to node I think, since 
				//  any nodes after that won't be dominated since they come before
				if let Some(follow) = post_order.find(|&index|
					self.graph.edges_directed(index, Direction::Incoming).count() >= 2
						&&
					dominators.immediate_dominator(index) == Some(node)
						&& // don't want a loop header that only lies on one of the branches to be the follow node
					self.loop_head.get(&index) != Some(&index)

				) {
					// Set the follow node of all unresolved nodes that lie between the head and the follow
					self.if_follow.insert(node, follow);
					let mut resolved = Vec::new();
					while let Some(n) = post_order.next() {
						if n == node {
							break;
						}
						if unresolved.remove(&n) {
							self.if_follow.insert(n, follow);
							resolved.push(n.index());
						}
					}
					trace!("If follow node found for {}: {}. Inserting {:?}", 
						node.index(), follow.index(), resolved);
				} else {
					unresolved.insert(node);
				}
			}
		}
		if !unresolved.is_empty() {
			warn!("Unresolved 2-way nodes: {:?}", set2vec(&unresolved));
		}
	}

	// If a node is a header or latching node,
	//  it will have itself as the corresponding node
	fn is_head_latch(&self, node: NodeIndex) -> bool {
		self.loop_head.get(&node) == Some(&node) ||
		self.loop_latch.get(&node) == Some(&node)
	}


	// TODO: check if needs rebuilding
	fn post_order(&mut self) -> Vec<NodeIndex> {
		if self.post_order.is_empty() {
			trace!("Computing post order traversal...");
			self.post_order = DfsPostOrder::new(&self.graph, self.entry).iter(&self.graph).collect();
		}

		self.post_order.clone()
	}
}

impl ControlFlowGraph {
	pub fn write_graph<F: Write>(&self, out: &mut F) -> Result<()> {
		let dot = Dot::with_config(&self.graph, &[DotCfg::NodeIndexLabel, DotCfg::EdgeNoLabel]);
		write!(out, "{:?}", dot)?;
		Ok(())
	}
}

// Replace ref
impl ControlFlowGraph {
	pub fn replace_ref(&mut self, global_vars: &[Variable], functions: &[Function], local_vars: &[Variable]) {
		trace!("Replacing references..");
		for block in self.graph.node_weights_mut() {
			for inst in block.instructions.iter_mut() {
				inst.replace_ref(global_vars, functions, local_vars);
			}
			block.condition.as_mut().map(|expr| expr.replace_ref(global_vars, functions, local_vars));
		}
	}
}


struct StatementConstructor {
	block_done: HashSet<NodeIndex>,
	if_follow: Vec<NodeIndex>,
	latch_node: Vec<NodeIndex>,
	gotos: HashSet<NodeIndex>,
}

impl StatementConstructor {
	fn new() -> StatementConstructor {
		StatementConstructor {
			block_done: HashSet::new(),
			if_follow: Vec::new(),
			latch_node: Vec::new(),
			gotos: HashSet::new(),
		}
	}

	fn construct_statements(&mut self, cfg: &ControlFlowGraph, entry: NodeIndex) -> Vec<Statement> {
		let mut result = Vec::new();

		let mut block_id = Some(entry);

		let mut line_num = None;

		// Construct entry differently
		if !cfg.is_function && entry == cfg.entry {
			let follow = cfg.if_follow.get(&entry).cloned();

			let mut entry_statement = EntryStatement::new();

			if let Some(follow) = follow {
				self.if_follow.push(follow);
			}
			let mut succ = cfg.graph.neighbors(entry).detach();
			while let Some((edge_index, node_index)) = succ.next(&cfg.graph) {
				let edge = cfg.graph[edge_index];
				if let GraphEdge::Entry(z_level) = edge {
					let block = self.construct_statements(cfg, node_index);
					entry_statement.add_entry(z_level, block);
				} else {
					error!("Entry has edge {:?}", edge);
				}
			}
			self.if_follow.pop();

			result.push(Statement {
				s_type: StatementType::Entry(entry_statement),
				line_num: None
			});

			block_id = follow;
		}

		while let Some(index) = block_id {
			let block = &cfg.graph[index];

			// Break if reached the follow node *BEFORE* visiting
			if self.if_follow.last() == Some(&index) {
				break;
			} else if self.block_done.contains(&index) {
				result.push(Statement::goto(index));
				self.gotos.insert(index);
				break;
			}

			result.push(Statement::label(index));
			self.block_done.insert(index);

			// Handle header nodes of loops separately
			if let Some(ref loop_ref) = cfg.loops.iter().find(|&ref loop_ref| loop_ref.head == index) {
				if loop_ref.head == loop_ref.latch {
					panic!("TODO: Loops where the header is the latch node.");
				}
				let loop_statement = match loop_ref.loop_type {
					// Pre-tested:
					// A<--.
					// |\  |
					// | \ |
					// |  \|
					// C   B
					// Before: A
					// Condition: A if else block is C, else negate(A)
					// Body: B + A
					LoopType::PreTested => {
						let mut loop_before = Vec::new();
						for inst in block.instructions.iter() {
							if let &Instruction::Line(line) = inst {
								line_num = Some(line as usize);
							} else {
								loop_before.push(Statement::new(inst.clone(), line_num.take()));
							}
						}
						result.extend(loop_before.clone());
						
						let (then_index, else_index) = cfg.get_then_else(loop_ref.head).unwrap();
						let (succ, condition) = if loop_ref.loop_follow == else_index {
							(then_index, loop_ref.condition.clone())
						} else {
							(else_index, loop_ref.condition.clone().negate())
						};

						self.latch_node.push(loop_ref.latch);
						let mut loop_contents = self.construct_statements(cfg, succ);
						self.latch_node.pop();


						loop_contents.extend(loop_before);
						Statement {
							s_type: StatementType::Loop(LoopStatement::While {
								condition,
								body: loop_contents
							}),
							line_num: None
						}
					},
					// Post-tested:
					// A<--.
					//  \  |
					//   \ |
					//    \|
					//     B ---> C
					// Before: Nothing
					// Condition: B if else block is C, else negate(B)
					// Body: A + B
					LoopType::PostTested => {
						let mut loop_contents = Vec::new();
						for inst in block.instructions.iter() {
							if let &Instruction::Line(line) = inst {
								line_num = Some(line as usize);
							} else {
								loop_contents.push(Statement::new(inst.clone(), line_num.take()));
							}
						}

						self.latch_node.push(loop_ref.latch);
						let succ = cfg.graph.neighbors(index).next().unwrap();
						loop_contents.extend(self.construct_statements(cfg, succ));
						self.latch_node.pop();


						// Negate the condition if the loop breaks when it is true
						//	i.e. the `then` block is outside the loop
						let (_, else_index) = cfg.get_then_else(loop_ref.latch).unwrap();

						let condition = if loop_ref.loop_follow == else_index {
							loop_ref.condition.clone()
						} else {
							loop_ref.condition.clone().negate()
						};

						Statement {
							s_type: StatementType::Loop(LoopStatement::DoWhile {
								condition,
								body: loop_contents
							}),
							line_num: None
						}
					},
					LoopType::Endless => panic!("Endless loop statement!"),
				};

				// Continue with follow
				result.push(loop_statement);
				block_id = Some(loop_ref.loop_follow);
			} else {
				for inst in block.instructions.iter() {
					if let &Instruction::Line(line) = inst {
						line_num = Some(line as usize);
					} else {
						result.push(Statement::new(inst.clone(), line_num.take()));
					}
				}

				// Break if reached the latch node *AFTER* visiting
				if self.latch_node.last() == Some(&index) {
					break;
				}


				let mut succ = cfg.graph.neighbors(index);
				match succ.clone().count() {
					0 | 1 => block_id = succ.next(),
					2 => {
						let if_statement = {
							let (then_index, else_index) = cfg.get_then_else(index).unwrap();

							// TODO: clean this
							// Check if it is of the form
							// if (cond) {
							//	 <then node>
							// }
							// <follow node>
							let (then_block, else_block, condition) = {
								let mut condition = block.condition.clone().unwrap_or(Expression::Error);
								if let Some(&block_follow) = cfg.if_follow.get(&index) { 
									let mut empty_then = false;

									let mut then_block;
									// TODO: find a proper way to do this
									if self.block_done.contains(&then_index) {
										then_block = vec![Statement::goto(then_index)];
										self.gotos.insert(then_index);
									} else if then_index != block_follow {
										self.if_follow.push(block_follow);
										then_block = self.construct_statements(cfg, then_index);
										self.if_follow.pop();
									} else {
										// then clause is the follow node
										// if (condition) {
										// } else {
										//   do_something();
										// }
										// do_follow();
										empty_then = true;
										condition = condition.negate();
										self.if_follow.push(block_follow);
										then_block = self.construct_statements(cfg, else_index);
										self.if_follow.pop();
									};

									let mut else_block;
									if self.block_done.contains(&else_index) {
										if !empty_then {	// didn't just write it
											else_block = Some(vec![Statement::goto(else_index)]);
											self.gotos.insert(else_index);
										} else {
											else_block = None;
										}
									} else if else_index != block_follow {
										self.if_follow.push(block_follow);
										else_block = Some(self.construct_statements(cfg, else_index));
										self.if_follow.pop();
									} else {
										else_block = None;
									};

									(then_block, else_block, condition)
								} else { // No follow, emit if..then..else
									let then_block = self.construct_statements(cfg, then_index);
									let else_block = Some(self.construct_statements(cfg, else_index));
									(then_block, else_block, condition)
								}
							};

							IfStatement::new(condition, then_block, else_block)
						};

						let if_statement = Statement {
							s_type: StatementType::If(if_statement),
							line_num: line_num.take()
						};
						result.push(if_statement);
						block_id = cfg.if_follow.get(&index).cloned();
					},
					_ => panic!("No non-entry switches!")
				}
			}

		}

		if let Some(num) = line_num {
			warn!("Unused line number {}", num);
		}

		result
	}
}

// Returns a list of intervals.
// The first one will be the interval with `entry` as header
fn compute_intervals<N, E>(graph: &Graph<N, E>, entry: NodeIndex) -> Vec<Interval> {
	let mut work_list = vec![entry];

	let mut intervals = Vec::new();
	let mut heads = HashSet::new();

	// Compute list of intervals
	while let Some(head) = work_list.pop() {
		if heads.contains(&head) {
			continue;
		}
		
		heads.insert(head);

		let mut interval = Interval::new(head);

		// Add all nodes that are dominated by this header
		//  We find all successors of nodes in the interval that are outside the interval
		//  and add them if all their predecessors are inside the interval
		//  Repeat until there is none to be added
		let mut changed = true;
		while changed {
			changed = false;
			let succ: Vec<NodeIndex> = interval.successors(graph);

			for node in succ {
				// Check if all predecessors are in the interval
				let mut pred = graph.neighbors_directed(node, Direction::Incoming);
				if pred.all(|p| interval.contains(&p)) {
					interval.add_node(node);
					changed = true;
				}
			}
		}

		// Add any nodes that are not in interval but have a predecessor in it to worklist
		for node in interval.successors(graph) {
			work_list.push(node);
		}

		// Compute the end node of the interval
		interval.compute_end(graph);

		intervals.push(interval);
	}

	intervals
}


type IntervalGraph = (Graph<NodeIndex, bool>, Vec<Interval>);
type DerivedSequence = Vec<IntervalGraph>;

fn derived_sequence<N, E>(g: &Graph<N, E>, mut entry: NodeIndex) -> DerivedSequence {
	trace!("Generating sequence of interval derived graphs...");

	let g1 = g.map(
		|node_index, _block| node_index,
		|_edge_index, _weight| true
	);
	trace!("\tConstructed graph G{}", 1);

	// TODO: might just not need this by searching for `externals`
	// Set entry to be the node index that has entry as weight
	entry = g1.node_references().find(|(_new, &old)| old == entry).unwrap().0;

	let mut deriv_seq = Vec::new();
	let mut last_graph = g1;

	let mut i = 2;
	'construct: loop {
		// Construct the next graph
		let graph = {
			// int_idx[node] gets the index of interval with header `node`
			let mut int_idx: HashMap<NodeIndex, NodeIndex> = HashMap::new();
			let mut graph = Graph::new();

			// Add nodes
			let intervals = compute_intervals(&last_graph, entry);
			for interval in intervals.iter() {
				int_idx.insert(interval.header, graph.add_node(interval.header));
			}
			// Add edges
			let mut edges = Vec::new();
			for (node, head) in graph.node_references() {
				let interval = intervals.iter().find(|i| &i.header == head).unwrap();
				// Use the last graph to get the successors of nodes inside this interval
				for succ_head in interval.successors(&last_graph) {
					edges.push((node, int_idx[&succ_head]));
				}
			}
			for edge in edges {
				graph.update_edge(edge.0, edge.1, true);
			}

			// Update entry to the node index of the interval containing entry
			// In this implementation, I think it's always NodeIndex(0)
			entry = int_idx[&entry];

			// Append (last_graph, intervals)
			deriv_seq.push((last_graph, intervals));

			graph
		};

		// If needed, use `is_isomorphic_matching`
		if is_isomorphic(&graph, &deriv_seq.last().unwrap().0) {
			break 'construct;
		}

		last_graph = graph;
		trace!("\tConstructed graph G{}", i);
		trace!("\t\t{:?}", last_graph);
		i += 1;
	}

	let reducible = deriv_seq.last().unwrap().0.node_count() == 1;
	trace!("Generated sequence of {} graphs. The final graph was {}.", deriv_seq.len(), if reducible { "reducible" } else { "irreducible"});

	deriv_seq
}

#[derive(Debug)]
struct Interval {
	header: NodeIndex,
	nodes: HashSet<NodeIndex>,
	end: NodeIndex,
}

impl Interval {
	fn new(header: NodeIndex) -> Interval {
		let mut nodes = HashSet::new();
		nodes.insert(header);
		Interval {
			header,
			nodes,
			end: header
		}
	}

	fn contains(&self, index: &NodeIndex) -> bool {
		self.nodes.contains(index)
	}

	fn add_node(&mut self, index: NodeIndex) {
		self.nodes.insert(index);
	}
	// The nodes (indices) of `graph` must match the nodes in `nodes`
	fn successors<'a, N, E>(&'a self, graph: &Graph<N, E>) -> Vec<NodeIndex> {
		let succ: HashSet<NodeIndex> = self.nodes.iter().flat_map(|&index| {
			graph.neighbors_directed(index, Direction::Outgoing)
		}).collect();

		succ.difference(&self.nodes).cloned().collect()
	}
}

struct Loop {
	head: NodeIndex,
	latch: NodeIndex,
	nodes: HashSet<NodeIndex>,
	loop_type: LoopType,
	loop_follow: NodeIndex,
	condition: Expression,
}

#[derive(Debug, PartialEq)]
enum LoopType {
	PreTested,
	PostTested,
	Endless
}


// Basic Blocks
struct Block {
	address: usize,

	traversed: bool,

	instructions: Vec<Instruction>,
	condition: Option<Expression>,
}

impl Block {
	fn new(address: usize) -> Self {
		Block {
			address,

			traversed: false,

			instructions: Vec::new(),
			condition: None,
		}
	}

	fn add_inst(&mut self, inst: Instruction) {
		self.instructions.push(inst);
	}
}

impl std::fmt::Debug for Block {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{:0x}", self.address)
	}
}

// Instructions
#[derive(Clone)]
pub enum Instruction {
	Line(u32),
	Binding { lhs: Expression, rhs: Expression },
	AddText(Expression, u32),
	SetName(Expression),
	Return(Vec<Expression>),
	Expression(Expression),
	Nop(u8)
}

impl Instruction {
	fn replace_ref(&mut self, global_vars: &[Variable], functions: &[Function], local_vars: &[Variable]) {
		match *self {
			Instruction::Binding { ref mut lhs, ref mut rhs } => {
				lhs.replace_ref(global_vars, functions, local_vars);
				rhs.replace_ref(global_vars, functions, local_vars);
			},
			Instruction::AddText(ref mut expr, _) => expr.replace_ref(global_vars, functions, local_vars),
			Instruction::SetName(ref mut expr) => expr.replace_ref(global_vars, functions, local_vars),
			Instruction::Return(ref mut vec) => for expr in vec.iter_mut() {
				expr.replace_ref(global_vars, functions, local_vars);
			},
			Instruction::Expression(ref mut expr) => expr.replace_ref(global_vars, functions, local_vars),
			Instruction::Line(_) => (),
			Instruction::Nop(_) => (),
		}
	}
}

impl std::fmt::Display for Instruction {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Instruction::Line(num) => write!(f, "line {}", num),
			Instruction::Binding { ref lhs, ref rhs } => write!(f, "{} = {}", lhs, rhs),
			Instruction::AddText(ref text, id) => write!(f, "addtext {}, {}", text, id),
			Instruction::SetName(ref name) => write!(f, "setname {}", name),
			Instruction::Return(ref args) =>
				if args.is_empty() {
					write!(f, "return")
				} else {
					write!(f, "return({})", format_list(args))
				},
			Instruction::Expression(ref expr) => {
				// If the expression is a variable, treat it as a declaration
				if let Expression::Variable(Variable { ref name, ref var_type }) = expr {
					write!(f, "{} {}", var_type, name)
				} else {
					write!(f, "{}", expr)
				}
			}
			Instruction::Nop(op) => write!(f, "nop {:#2x}", op)
		}
	}
}

//======================================================================

// These aren't really statements, I picked a bad name
#[derive(Clone)]
pub struct Statement {
	s_type: StatementType,
	line_num: Option<usize>,
}

#[derive(Clone)]
enum StatementType {
	Inst(Instruction),
	If(IfStatement),
	Loop(LoopStatement),
	Goto(NodeIndex),
	Label(NodeIndex),
	Entry(EntryStatement)
}

#[derive(Clone)]
struct IfStatement {
	condition: Expression,
	then_block: Vec<Statement>,
	else_block: Option<Vec<Statement>>
}

impl IfStatement {
	fn new(condition: Expression, then_block: Vec<Statement>, else_block: Option<Vec<Statement>>) -> Self {
		if let Some(ref v) = else_block {
			if v.is_empty() {
				return IfStatement {
					condition,
					then_block,
					else_block: None
				}
			}
		}

		IfStatement {
			condition,
			then_block,
			else_block
		}
	}
	fn apply_func_to_blocks<F>(&mut self, mut func: F)
	where 
		F: FnMut(&mut Vec<Statement>) -> (),
	{
		func(&mut self.then_block);
		if let Some(ref mut block) = self.else_block {
			func(block);
		}
	}
}

#[derive(Clone)]
enum LoopStatement {
	While {
		condition: Expression,
		body: Vec<Statement>
	},
	DoWhile {
		condition: Expression,
		body: Vec<Statement>
	},
	For {
		// Header
		init: Option<Instruction>,
		condition: Expression,
		after: Option<Instruction>,

		body: Vec<Statement>,
	}
}

impl LoopStatement {
	fn write<F: Write>(&self, out: &mut F, indent: usize, comment: String) -> Result<()> {
		match *self {
			LoopStatement::While { ref condition, ref body } => {
				write!(out, "{}while ({}) {{ {}\n", "\t".repeat(indent), condition, comment)?;
				for s in body.iter() {
					s.write(out, indent + 1)?;
				}
				write!(out, "{}}} \n", "\t".repeat(indent))?;
			},
			LoopStatement::DoWhile { ref condition, ref body } => {
				write!(out, "{}do {{ {}\n", "\t".repeat(indent), comment)?;
				for s in body.iter() {
					s.write(out, indent + 1)?;
				}
				write!(out, "{}}} while ({}) \n", "\t".repeat(indent), condition)?;
			},
			LoopStatement::For { ref init, ref condition, ref after, ref body } => {
				let init_str = if let Some(inst) = init { format!("{}", inst) } else { String::new() };
				let next_str = if let Some(inst) = after { format!("{}", inst) } else { String::new() };
				
				write!(out, "{}for({};{};{}) {{ {}\n", "\t".repeat(indent), init_str, condition, next_str, comment)?;
				for s in body.iter() {
					s.write(out, indent + 1)?;
				}
				write!(out, "{}}} \n", "\t".repeat(indent))?;
			},
		}
		Ok(())
	}

	fn apply_func_to_blocks<F>(&mut self, mut func: F)
	where 
		F: FnMut(&mut Vec<Statement>) -> (),
	{
		match self {
			LoopStatement::While { ref mut body, .. } => func(body),
			LoopStatement::DoWhile { ref mut body, .. } => func(body),
			LoopStatement::For { ref mut body, .. } => func(body),

		}
	}
}

#[derive(Clone)]
struct EntryStatement {
	entries: Vec<(usize, Vec<Statement>)>
}

impl EntryStatement {
	fn new() -> Self {
		EntryStatement {
			entries: Vec::new()
		}
	}

	fn add_entry(&mut self, z_level: usize, block: Vec<Statement>) {
		self.entries.push((z_level, block));
	}

	fn apply_func_to_blocks<F>(&mut self, mut func: F)
	where 
		F: FnMut(&mut Vec<Statement>) -> (),
	{
		for &mut (_, ref mut block) in self.entries.iter_mut() {
			func(block);
		}
	}
}


impl Statement {
	fn new(inst: Instruction, line_num: Option<usize>) -> Statement {
		Statement {
			s_type: StatementType::Inst(inst),
			line_num
		}
	}

	fn goto(block: NodeIndex) -> Statement {
		warn!("Creating a goto for block {}", block.index());
		Statement {
			s_type: StatementType::Goto(block),
			line_num: None
		}
	}

	fn label(block: NodeIndex) -> Statement {
		Statement {
			s_type: StatementType::Label(block),
			line_num: None
		}
	}

	pub fn write<F: Write>(&self, out: &mut F, indent: usize) -> Result<()> {
		let comment = if let Some(line_num) = self.line_num {
			format!("// line {}", line_num)
		} else {
			"".to_string()
		};
		match self.s_type {
			StatementType::Inst(ref inst) => write!(out, "{}{} {}\n", "\t".repeat(indent), inst, comment)?,
			StatementType::If(ref statement) => {
				write!(out, "{}if ({}) {{ {}\n", "\t".repeat(indent), statement.condition, comment)?;
				for s in statement.then_block.iter() {
					s.write(out, indent + 1)?;
				}

				if let Some(ref block) = statement.else_block {
					write!(out, "{}}} else {{\n", "\t".repeat(indent))?;
					for s in block.iter() {
						s.write(out, indent + 1)?;
					}
				}
				write!(out, "{}}}\n", "\t".repeat(indent))?;
			},
			StatementType::Entry(ref statement) => {
				write!(out, "{}Entry {{ \n", "\t".repeat(indent))?;
				for &(z_level, ref block) in statement.entries.iter().rev() {
					write!(out, "{}z {}: \n", "\t".repeat(indent), z_level)?;
					for s in block.iter() {
						s.write(out, indent + 1)?;
					}
				}
				write!(out, "{}}} \n", "\t".repeat(indent))?;
			},
			StatementType::Loop(ref statement) => statement.write(out, indent, comment)?,
			StatementType::Goto(block) => write!(out, "{}goto label_{} \n", "\t".repeat(indent), block.index())?,
			StatementType::Label(block) => write!(out, "{}label_{}: \n", "\t".repeat(indent), block.index())?,
		}
		Ok(())
	}
}


// Simplification
fn simplify_statements(block: &mut Vec<Statement>, ctor: &StatementConstructor) {
	remove_labels(block, &ctor.gotos);

	construct_for_loops(block);

	//fold_ifs(block);
}

fn remove_labels(statements: &mut Vec<Statement>, gotos: &HashSet<NodeIndex>) {
	// poor man's retain_mut/drain_filter
	let mut i = 0;
	while i != statements.len() {
		let to_remove = {
			let s = &mut statements[i];
			match s.s_type {
				StatementType::Label(ref label) => !gotos.contains(label),
				StatementType::If(ref mut statement) => {statement.apply_func_to_blocks(|block| remove_labels(block, gotos)); false},
				StatementType::Loop(ref mut statement) => {statement.apply_func_to_blocks(|block| remove_labels(block, gotos)); false},
				StatementType::Entry(ref mut statement) => {statement.apply_func_to_blocks(|block| remove_labels(block, gotos)); false},
				StatementType::Inst(_) => false,
				StatementType::Goto(_) => false,
			}
		};
		if to_remove {
			statements.remove(i);
		} else {
			i += 1;
		}
	}
}

fn construct_for_loops(block: &mut Vec<Statement>) {
	// Contruct for loops from the following
	//	if (some_condition) {
	//		do {
	//			do_something();
	//		} while (some_condition);
	//	}
	//	=>
	//	for (;some_condition;) {
	//		do_something();
	//	}
	// TODO: clean up this mess
	for s in block.iter_mut() {
		let s_type = &mut s.s_type;
		let for_loop = match *s_type {
			StatementType::If(ref mut statement) => 
				convert_if_to_for(statement)
					.or_else(|| {statement.apply_func_to_blocks(construct_for_loops); None}),
			StatementType::Loop(ref mut statement) => {statement.apply_func_to_blocks(construct_for_loops); None},
			_ => None,
		};

		if let Some(s) = for_loop {
			std::mem::replace(s_type, StatementType::Loop(s));
		}
	}

	// Leaves the if statement in a broken state if Some(Loop) is returned
	fn convert_if_to_for(if_statement: &mut IfStatement) -> Option<LoopStatement> {
		if if_statement.then_block.len() != 1 || !if_statement.else_block.is_none() {
			return None;
		}
		let if_cond = &if_statement.condition;
		if let Statement { s_type: StatementType::Loop(ref mut loop_statement), ..} = if_statement.then_block[0] {
			if let LoopStatement::DoWhile { condition, body } = loop_statement {
				if condition == if_cond {
					construct_for_loops(body);

					return Some(LoopStatement::For {
						init: None,
						condition: std::mem::replace(condition, Expression::Error),
						after: None,
						body: std::mem::replace(body, Vec::new())
					});
				}
			}
		}
		None
	}
}

// fn fold_ifs(block: &mut Vec<Statement>) {
// 	for s in block.iter_mut() {
// 		match s.s_type {
// 			StatementType::If(ref mut statement) => {

// 			},
// 			StatementType::Loop(ref mut statement) => statement.apply_func_to_blocks(fold_ifs),
// 			_ => {},
// 		};
// 	}
// }

// Util
fn set2vec(set: &HashSet<NodeIndex>) -> Vec<usize> {
	set.iter().cloned().map(NodeIndex::index).collect::<Vec<usize>>()
}

// Kind of better
// Kind of more general too
// Still wrong
// =============================================================================
impl Interval {
	// TODO: type check
	fn compute_end<N, E>(&mut self, graph: &Graph<N, E>) {
		for &node in self.nodes.iter() {
			let mut succ = graph.neighbors_directed(node, Direction::Outgoing);
			if succ.any(|idx| !self.nodes.contains(&idx)) {
				self.end = node;
			}
		}
	}

	// index - index to node in the root graph
	// seq - a slice of a DerivedSequence where the last element contains a graph that matches these nodes
	// checks nested
	fn contains_root(&self, index: &NodeIndex, seq: &[IntervalGraph]) -> bool {
		if seq.len() > 1 {
			let graph = &seq.last().unwrap().0;
			let vec = &seq[seq.len() - 2].1;
			for &node in self.nodes.iter() {
				// Find the interval with the header that is this node
				let header = graph[node];
				let interval = vec.iter().find(|itvl| itvl.header == header).unwrap();
				if interval.contains_root(index, &seq[..seq.len() - 1]) {
					return true;
				}
			}
			false
		} else {
			self.nodes.contains(index)
		}
	}
}

// Node: Node index matching last element of seq
// Returns node index for root
fn get_head(node: NodeIndex, seq: &[IntervalGraph]) -> NodeIndex {
	if let Some((graph, vec)) = seq.last() {
		let header = graph[node];
		get_head(header, &seq[..seq.len() - 1])
	} else {
		node
	}
}

// Node: Node index matching last element of seq
// Returns node index for root
fn get_end(node: NodeIndex, seq: &[IntervalGraph]) -> NodeIndex {
	if seq.len() > 1 {
		let vec = &seq[seq.len() - 2].1;
		let graph = &seq.last().unwrap().0;
		let interval = vec.iter().find(|itvl| itvl.header == graph[node]).unwrap();
		get_end(interval.end, &seq[..seq.len() - 1])
	} else {
		let graph = &seq.last().unwrap().0;
		graph[node]
	}
}

impl ControlFlowGraph {
	fn structure_loops(&mut self) {
		trace!("Structuring loops...");
		let deriv_seq = derived_sequence(&self.graph, self.entry);

		for (i, (graph, intervals)) in deriv_seq.iter().enumerate() {
			// For each interval header, check if any of its predecessors
			// are inside that interval
			for interval in intervals.iter() {
				let header = graph[interval.header];
				let mut pred = graph.neighbors_directed(header, Direction::Incoming);
				// TODO: && not in_loop(p)
				if let Some(latching_node) = pred.find(|p| interval.contains(p)) {
					self.add_loop(header, latching_node, &interval, &deriv_seq[..i + 1]);
				}
			}
		}
	}

	fn add_loop(&mut self, head: NodeIndex, latch: NodeIndex, interval: &Interval, deriv_seq: &[IntervalGraph]) {
		let head = get_head(head, deriv_seq);
		let latch = get_end(latch, deriv_seq);

		let mut nodes_in_loop = HashSet::new();
			nodes_in_loop.insert(head);

		self.loop_head.insert(head, head);
		self.loop_latch.insert(latch, latch);
		// Iterate through head + 1 to latch
		let mut rpo = self.post_order().into_iter().rev();
		rpo.find(|&node| node == head);	// `find` consumes the one found and continues on the next one
		while let Some(node) = rpo.next() {
			if interval.contains_root(&node, deriv_seq) {
				nodes_in_loop.insert(node);
				self.loop_head.entry(node).or_insert(head);
				self.loop_latch.entry(node).or_insert(latch);
			}

			if node == latch {
				break;
			}
		}

		// Find loop type
		let loop_type = {
			let num_succ_latch = self.graph.neighbors(latch).count();
			let num_succ_head = self.graph.neighbors(head).count();

			if num_succ_latch >= 2 {
				if num_succ_head >= 2 {
					let mut succ = self.graph.neighbors(head);
					let succ_1 = succ.next().unwrap();
					let succ_2 = succ.next().unwrap();
					if nodes_in_loop.contains(&succ_1) && nodes_in_loop.contains(&succ_2) {
						LoopType::PostTested
					} else {
						LoopType::PreTested
					}
				} else {
					LoopType::PostTested
				}
			} else {
				if num_succ_head == 2 {
					LoopType::PreTested
				} else {
					LoopType::Endless
				}
			}
		};

		// Find loop follow - currently this is wrong and might pick a node that is earlier
		let loop_follow = {
			match loop_type {
				LoopType::PreTested => {
					let mut succ = self.graph.neighbors(head);
					let succ_1 = succ.next().unwrap();
					if nodes_in_loop.contains(&succ_1) {
						succ.next().unwrap()
					} else {
						succ_1
					}
				}, 
				LoopType::PostTested => {
					let mut succ = self.graph.neighbors(latch);
					let succ_1 = succ.next().unwrap();
					if nodes_in_loop.contains(&succ_1) {
						succ.next().unwrap()
					} else {
						succ_1
					}
				},
				_ => panic!()
			}
		};

		let condition = {
			match loop_type {
				LoopType::PreTested => {
					self.graph[head].condition.clone().unwrap_or(Expression::Error)
				}, 
				LoopType::PostTested => {
					self.graph[latch].condition.clone().unwrap_or(Expression::Error)
				},
				_ => panic!()
			}
		};

		println!("Found {:?} - Head: {}, Latch: {}, Follow: {}, Nodes: {:?}", loop_type, head.index(), latch.index(), loop_follow.index(), set2vec(&nodes_in_loop));

		self.loops.push(Loop {
			head,
			latch,
			nodes: nodes_in_loop,
			loop_type,
			loop_follow,
			condition
		});
	}
}