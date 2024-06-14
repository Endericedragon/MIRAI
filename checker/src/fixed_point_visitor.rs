// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use crate::abstract_value::{AbstractValue, AbstractValueTrait};
use crate::block_visitor::BlockVisitor;
use crate::body_visitor::BodyVisitor;
use crate::environment::Environment;
use crate::options::DiagLevel;
use crate::{abstract_value, k_limits};
use log_derive::*;
use mirai_annotations::*;
use rpds::{HashTrieMap, HashTrieSet};
use rustc_data_structures::graph::dominators::Dominators;
use rustc_middle::mir;
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Formatter, Result};
use std::rc::Rc;

pub struct FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx> {
    pub bv: &'fixed mut BodyVisitor<'analysis, 'compilation, 'tcx>,
    already_visited: HashTrieSet<mir::BasicBlock>,
    pub block_indices: Vec<mir::BasicBlock>,
    loop_anchors: HashSet<mir::BasicBlock>,
    dominators: Dominators<mir::BasicBlock>,
    /// in_state\[bb\] is the join (or widening) of the out_state values of each predecessor of bb
    in_state: HashMap<mir::BasicBlock, Environment>,
    /// out_state\[bb\] is the environment that results from analyzing block bb, given in_state[bb]
    out_state: HashMap<mir::BasicBlock, Environment>,
    pub terminator_state: HashMap<mir::BasicBlock, Environment>,
}

impl<'fixed, 'analysis, 'compilation, 'tcx> Debug
    for FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "FixedPoint".fmt(f)
    }
}

/// A visitor that simply traverses enough of the MIR associated with a particular code body
/// so that we can test a call to every default implementation of the MirVisitor trait.
impl<'fixed, 'analysis, 'compilation, 'tcx>
    FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx>
{
    #[logfn_inputs(TRACE)]
    pub fn new(
        body_visitor: &'fixed mut BodyVisitor<'analysis, 'compilation, 'tcx>,
    ) -> FixedPointVisitor<'fixed, 'analysis, 'compilation, 'tcx> {
        //? 这儿的Dominator好像和编译原理中的“基本块支配关系”有关
        //? 例如基本块A在B前面，但是B又能“控制”A，那么A和B之间就形成了循环
        let dominators = body_visitor.mir.basic_blocks.dominators();
        let (block_indices, loop_anchors) = get_sorted_block_indices(body_visitor.mir, dominators);
        // in_state[bb] is the join (or widening) of the out_state values of each predecessor of bb
        let mut in_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // out_state[bb] is the environment that results from analyzing block bb, given in_state[bb]
        let mut out_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        // terminator_state[bb] is the environment that should be used to error check the terminator of bb
        let mut terminator_state: HashMap<mir::BasicBlock, Environment> = HashMap::new();
        for bb in block_indices.iter() {
            in_state.insert(*bb, Environment::default());
            out_state.insert(*bb, Environment::default());
            terminator_state.insert(*bb, Environment::default());
        }
        FixedPointVisitor {
            already_visited: HashTrieSet::new(),
            bv: body_visitor,
            block_indices,
            loop_anchors,
            dominators: dominators.clone(),
            in_state,
            out_state,
            terminator_state,
        }
    }

    /// Visits each statement in order and then visits the terminator.
    #[logfn_inputs(TRACE)]
    pub fn visit_blocks(&mut self) {
        let blocks = self.block_indices.clone();
        for bb in blocks {
            // 检查self.bv是否已经完成分析或者超时。若未完成分析则break
            check_for_early_break!(self.bv);
            if !self.already_visited.contains(&bb) {
                if !self.loop_anchors.contains(&bb) {
                    // bb基本块是循环的入口
                    self.visit_basic_block(bb, 0);
                } else {
                    //? 不会是不动点吧？
                    self.compute_fixed_point(bb);
                }
            }
        }
    }

    /// Visits a single basic block, starting with an in_state that is the join of all of
    /// the out_state values of its predecessors and then updating out_state with the final
    /// current_environment of the block. Also adds the block to the already_visited set.
    #[logfn_inputs(TRACE)]
    fn visit_basic_block(&mut self, bb: mir::BasicBlock, iteration_count: usize) {
        // Merge output states of predecessors of bb
        // 先构造bb的入状态，这可以通过汇总bb的前驱基本块的出状态来实现
        let mut i_state = if iteration_count == 0 && bb.index() == 0 {
            // 直接套用最最初始的状态，可以想象这是一个没有前驱基本块的基本块，它是整个执行流的开头
            self.bv.first_environment.clone()
        } else {
            self.get_initial_state_from_predecessors(bb, iteration_count)
        };
        // Note that iteration_count is zero unless bb is a loop anchor.
        if iteration_count == 2 || iteration_count == 3 {
            // We do not have (and don't want to have) a way to distinguish the value of a widened
            // loop variable in one iteration from its value in the previous iteration, so
            // conditions involving loop variables are not referentially transparent
            // and we have to do without them. Also, only the conditions that flow into
            // the loop anchor at iteration 1 (i.e. before the loop body was executed the first time)
            // can be loop invariant (and thus apply to all executions of the loop body).
            let loop_variants = self.in_state[&bb].get_loop_variants(&i_state);
            let previous_state = &self.in_state[&bb];
            let invariant_entry_condition = previous_state
                .entry_condition
                .remove_conjuncts_that_depend_on(&loop_variants);
            i_state = if iteration_count == 2 {
                previous_state.join(i_state)
            } else {
                previous_state.widen(i_state)
            };
            i_state.entry_condition = invariant_entry_condition;
        } else if iteration_count > 3 {
            // From iteration 3 onwards, the entry condition is not affected by changes in the loop
            // body, so we just stick to the one computed in iteration 3.
            let invariant_entry_condition = self.in_state[&bb].entry_condition.clone();
            i_state = self.in_state[&bb].widen(i_state);
            i_state.entry_condition = invariant_entry_condition;
        }
        self.in_state.insert(bb, i_state.clone());
        self.bv.current_environment = i_state;
        let mut block_visitor = BlockVisitor::new(self.bv);
        block_visitor.visit_basic_block(bb, &mut self.terminator_state);
        self.out_state
            .insert(bb, self.bv.current_environment.clone());
        self.already_visited.insert_mut(bb);
    }

    /// Repeatedly evaluate the loop body starting at loop_anchor until widening
    /// kicked in and a fixed point has been reached.
    #[logfn_inputs(TRACE)]
    fn compute_fixed_point(&mut self, loop_anchor: mir::BasicBlock) -> mir::BasicBlock {
        let saved_already_visited = self.already_visited.clone();
        let saved_fresh_variable_offset = self.bv.fresh_variable_offset;
        let mut iteration_count = 1;
        let mut changed = true;
        let mut last_block = loop_anchor;
        // Iterate at least 4 times so that widening kicks in for loop variables and at least
        // two iterations were performed starting with widened variables.
        while iteration_count <= 4 || changed {
            self.already_visited = saved_already_visited.clone();
            self.bv.fresh_variable_offset = saved_fresh_variable_offset;
            let result = self.visit_loop_body(loop_anchor, iteration_count);
            changed = result.0;
            last_block = result.1;
            check_for_early_break!(self.bv);
            if iteration_count >= k_limits::MAX_FIXPOINT_ITERATIONS {
                break;
            }
            iteration_count += 1;
        }
        if iteration_count >= k_limits::MAX_FIXPOINT_ITERATIONS {
            if changed {
                if self.bv.cv.options.diag_level == DiagLevel::Paranoid {
                    let span = self.bv.current_span;
                    let warning = self.bv.cv.session.struct_span_warn(
                        span,
                        format!(
                            "Fixed point loop iterations exceeded limit of {}",
                            k_limits::MAX_FIXPOINT_ITERATIONS
                        ),
                    );
                    self.bv.emit_diagnostic(warning);
                } else {
                    warn!(
                        "Fixed point loop iterations {} exceeded limit of {} at {:?} in function {}.",
                        iteration_count,
                        k_limits::MAX_FIXPOINT_ITERATIONS,
                        self.bv.current_span,
                        self.bv.function_name
                    );
                }
            } else {
                trace!(
                    "Fixed point loop iterations {} exceeded limit of {} at {:?} in function {}.",
                    iteration_count,
                    k_limits::MAX_FIXPOINT_ITERATIONS,
                    self.bv.current_span,
                    self.bv.function_name
                );
            }
        }
        last_block
    }

    /// Visits a loop body. Return true if the out_state computed by this visit is not a subset
    /// of the out_state computed previously. When it is a subset, a fixed point has been reached.
    /// A loop body is all of the blocks that are dominated by the loop anchor.
    #[logfn_inputs(TRACE)]
    fn visit_loop_body(
        &mut self,
        loop_anchor: mir::BasicBlock,
        iteration_count: usize,
    ) -> (bool, mir::BasicBlock) {
        let mut changed = false;
        // 目前last_block暂时是循环的入口基本块
        let mut last_block = loop_anchor;
        // self.block_indices其实就是从BodyVisitor中的MIR提取出来的所有基本块，而且经过了拓扑排序
        let blocks = self.block_indices.clone();
        // 是当前基本块的"出状态"，如果"出状态"变化，changed就会被设置为true
        let old_state = self.out_state.clone();
        for bb in blocks {
            // 遍历自身的所有基本块
            check_for_early_break!(self.bv);
            if !self.already_visited.contains(&bb) && self.dominators.dominates(loop_anchor, bb) {
                // 注意这儿last_block被重新赋值了
                // 由循环条件可知bb是受loop_anchor控制的，因此last_block永远是受loop_anchor控制的基本块
                last_block = bb;
                // Visit the next block, or the entire nested loop anchored by it.
                if bb == loop_anchor {
                    // 发现这个bb就是循环开头，那么直接访问该bb即可
                    self.visit_basic_block(bb, iteration_count); // join or widen
                } else if self.loop_anchors.contains(&bb) {
                    // 发现不止loop_ahcnor，这个bb自己也是一个循环的开头，于是递归地调用寻找不动点算法
                    last_block = self.compute_fixed_point(bb);
                } else {
                    // 除上述两种特殊情况外，其他情况都直接访问该bb
                    self.visit_basic_block(bb, 0); // conditional expressions
                }

                // Check for a fixed point, once two iterations with widened variables were executed.
                if iteration_count > 3
                    && !self.out_state[&last_block].subset(&old_state[&last_block])
                {
                    // self.out_state[last_block]变宽了，说明有些路径上的值发生了变化，需要重新分析
                    // There is some path for which self.bv.current_environment.value_at(path) includes
                    // a value this is not present in self.out_state[last_block].value_at(path), so any block
                    // that used self.out_state[bb] as part of its input state now needs to get reanalyzed.
                    changed = true;
                }
            }
        }
        (changed, last_block)
    }

    /// Join the exit states from all predecessors blocks to get the entry state fo this block.
    /// If a predecessor has not yet been analyzed, its state does not form part of the join.
    /// If no predecessors have been analyzed, the entry state is a default entry state with an
    /// entry condition of TOP.
    /// Note that iteration_count should be 0 except if bb is a loop anchor, in which case it
    /// is greater than 0.
    #[logfn_inputs(TRACE)]
    fn get_initial_state_from_predecessors(
        &mut self,
        bb: mir::BasicBlock,
        iteration_count: usize,
    ) -> Environment {
        let mut predecessor_states_and_conditions: Vec<(Environment, Rc<AbstractValue>)> =
            self.bv.mir.basic_blocks.predecessors()[bb]
                .iter()
                .filter_map(|pred_bb| {
                    // If the predecessor can only be reached via bb then bb and pred_bb are
                    // part of the loop body.
                    let is_loop_back = self.dominators.dominates(bb, *pred_bb);
                    if iteration_count == 1 && is_loop_back {
                        // For the first iteration of the loop body we only want state that
                        // precedes the body. Normally, the state of a block that is part of the
                        // loop body will still be in the default state in iteration 1
                        // and thus get ignored.
                        // If the loop is nested, however, there will be state from the previous
                        // iteration of the outer loop, so we have to explicitly ignore the state.
                        return None;
                    }
                    if iteration_count > 1 && !is_loop_back {
                        // Once the loop body has been interpreted in its initial state (iteration 1)
                        // we only want state from previous iterations of the loop.
                        return None;
                    }
                    let pred_state = &self.out_state[pred_bb];
                    if let Some(pred_exit_condition) = pred_state.exit_conditions.get(&bb) {
                        if pred_exit_condition.as_bool_if_known().unwrap_or(true) {
                            trace!(
                                "pred {:?} exits on condition {:?} with {:?}",
                                pred_bb,
                                pred_exit_condition,
                                pred_state
                            );
                            Some((pred_state.clone(), pred_exit_condition.clone()))
                        } else {
                            // If pred_bb is known to have a false exit condition for bb it can be ignored.
                            None
                        }
                    } else if let mir::BasicBlockData {
                        is_cleanup: true, ..
                    } = &self.bv.mir[bb]
                    {
                        // A clean up block does not execute starting with the normal exit state of
                        // a predecessor block. If the predecessor ends on a call, the side effects of
                        // the call should probably be used to havoc parts of the normal state of
                        // the predecessor. For now, just proceed as if the predecessor block had no
                        // effect on its initial state.
                        // todo: perhaps just leave function constants in the initial state.
                        Some((
                            self.terminator_state[pred_bb].clone(),
                            Rc::new(abstract_value::TRUE),
                        ))
                    } else {
                        // If pred_state does not have an exit condition map, it is in its default state
                        // which means it has not yet been visited, or it is code that is known to always
                        // panic at runtime. Either way, we don't want to include its out state here.
                        None
                    }
                })
                .collect();
        if predecessor_states_and_conditions.is_empty() {
            // bb is unreachable, at least in this iteration.
            // We therefore give it a false entry condition so that the block analyses knows
            // the block is unreachable.
            let mut initial_state = self.bv.first_environment.clone();
            initial_state.entry_condition = Rc::new(abstract_value::FALSE);
            return initial_state;
        }
        if predecessor_states_and_conditions.len() == 1 {
            let (mut state, entry_condition) = predecessor_states_and_conditions.remove(0);
            state.entry_condition = entry_condition;
            state.exit_conditions = HashTrieMap::default();
            state
        } else {
            let entry_condition = predecessor_states_and_conditions
                .iter()
                .map(|(_, c)| c.clone())
                .reduce(|c1, c2| c1.or(c2))
                .unwrap();
            trace!("entry_condition {:?}", entry_condition);
            let mut state = predecessor_states_and_conditions
                .into_iter()
                .reduce(|(state1, cond1), (state2, cond2)| {
                    (state2.conditional_join(state1, &cond2, &cond1), cond1)
                })
                .expect("one or more states to fold into something")
                .0;
            state.entry_condition = entry_condition;
            state
        }
    }
}

/// Do a topological sort, breaking loops by preferring lower block indices, using dominance
/// to determine if there is a loop (if a is predecessor of b and b dominates a then they
/// form a loop and we'll emit the one with the lower index first).
/// 拓扑排序，获得当前节点的所有前驱结点构成的图的拓扑排序，并求取其中的循环入口
/// 本质上是一个后序遍历，因此root_block会排在它的前驱节点后面
#[logfn_inputs(TRACE)]
fn add_predecessors_then_root_block<'tcx>(
    mir: &'tcx mir::Body<'tcx>,
    root_block: mir::BasicBlock,
    dominators: &Dominators<mir::BasicBlock>,
    loop_anchors: &mut HashSet<mir::BasicBlock>,
    block_indices: &mut Vec<mir::BasicBlock>,
    already_added: &mut HashSet<mir::BasicBlock>,
) {
    if !already_added.insert(root_block) {
        return;
    }
    for pred_bb in mir.basic_blocks.predecessors()[root_block].iter() {
        if already_added.contains(pred_bb) {
            continue;
        };
        // 通过前驱节点的控制关系找到循环的存在，并且将循环的入口加入loop_anchors集合中
        if dominators.dominates(root_block, *pred_bb) {
            // pred_bb has still to be added, so it has a greater index than root_block, making root_block the loop anchor.
            //todo: checked_assume!(root_block.index() < pred_bb.index());
            // Root block has a smaller index than pred_bb because it has not already been added.
            loop_anchors.insert(root_block);
            continue;
        }
        add_predecessors_then_root_block(
            mir,
            *pred_bb,
            dominators,
            loop_anchors,
            block_indices,
            already_added,
        );
    }
    assume!(block_indices.len() < std::usize::MAX); // We'll run out of memory long  before this overflows
    block_indices.push(root_block);
}

// Perform a topological sort on the basic blocks so that blocks are analyzed after their
// predecessors (except in the case of loop anchors).
#[logfn_inputs(TRACE)]
#[logfn(TRACE)]
fn get_sorted_block_indices<'tcx>(
    mir: &'tcx mir::Body<'tcx>,
    dominators: &Dominators<mir::BasicBlock>,
) -> (Vec<mir::BasicBlock>, HashSet<mir::BasicBlock>) {
    let mut block_indices = Vec::new();
    let mut already_added = HashSet::new();
    let mut loop_anchors = HashSet::new();
    for bb in mir.basic_blocks.indices() {
        add_predecessors_then_root_block(
            mir,
            bb,
            dominators,
            &mut loop_anchors,
            &mut block_indices,
            &mut already_added,
        );
    }
    (block_indices, loop_anchors)
}
