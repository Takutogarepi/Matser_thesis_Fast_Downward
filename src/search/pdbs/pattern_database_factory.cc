#include "pattern_database_factory.h"

#include "abstract_operator.h"
#include "match_tree.h"
#include "pattern_database.h"


#include "../algorithms/priority_queues.h"
#include "../task_utils/task_properties.h"
#include "../utils/math.h"
#include "../utils/rng.h"
#include "../utils/hash.h"
#include "../lp/lp_solver.h"

#include <algorithm>
#include <cassert>
#include <limits>
#include <vector>
#include <unordered_map>


using namespace std;

namespace pdbs {
class PatternDatabaseFactory {
    const TaskProxy &task_proxy;
    VariablesProxy variables;
    Projection projection;
    vector<int> variable_to_index;
    vector<AbstractOperator> abstract_ops;
    vector<FactPair> abstract_goals;
    vector<int> distances;
    vector<int> generating_op_ids;
    vector<vector<OperatorID>> wildcard_plan;

    void compute_variable_to_index(const Pattern &pattern);

    /*
      Abstract operators are built from concrete operators. The
      parameters follow the usual name convention of SAS+ operators,
      meaning prevail, preconditions and effects are all related to
      progression search.
    */
    AbstractOperator build_abstract_operator(
        const vector<FactPair> &prev_pairs,
        const vector<FactPair> &pre_pairs,
        const vector<FactPair> &eff_pairs,
        int concrete_op_id,
        int cost) const;

    /*
      Recursive method; called by build_abstract_operators_for_op. In the case
      of a precondition with value = -1 in the concrete operator, all
      multiplied out abstract operators are computed, i.e. for all
      possible values of the variable (with precondition = -1), one
      abstract operator with a concrete value (!= -1) is computed.
    */
    void multiply_out(
        int concrete_op_id,
        int pos,
        int cost,
        vector<FactPair> &prev_pairs,
        vector<FactPair> &pre_pairs,
        vector<FactPair> &eff_pairs,
        const vector<FactPair> &effects_without_pre,
        vector<AbstractOperator> &operators) const;

    /*
      Computes all abstract operators for a given concrete operator (by
      its global operator number). Initializes data structures for initial
      call to recursive method multiply_out. variable_to_index maps
      variables in the task to their index in the pattern or -1.
    */
    void build_abstract_operators_for_op(
        const OperatorProxy &op,
        int cost,
        vector<AbstractOperator> &operators) const;

    void compute_abstract_operators(const vector<int> &operator_costs);

    /*
      This creates a unique_ptr because MSVC 14.29 leaves MatchTree in
      an invalid state when using raw objects here, presumably because
      it cannot create a correct default move assignment operator for the
      Node class used by MatchTree.
    */
    unique_ptr<MatchTree> compute_match_tree() const;

    void compute_abstract_goals();

    /*
      For a given abstract state (given as index), the according values
      for each variable in the state are computed and compared with the
      given pairs of goal variables and values. Returns true iff the
      state is a goal state.
    */
    bool is_goal_state(int state_index) const;

    void compute_distances(const MatchTree &match_tree, bool compute_plan);

    void compute_plan(
        const MatchTree &match_tree,
        const shared_ptr<utils::RandomNumberGenerator> &rng,
        bool compute_wildcard_plan);

public:
    PatternDatabaseFactory(
        const TaskProxy &task_proxy,
        const Pattern &pattern,
        const vector<int> &operator_costs = vector<int>(),
        bool compute_plan = false,
        const shared_ptr<utils::RandomNumberGenerator> &rng = nullptr,
        bool compute_wildcard_plan = false);
    ~PatternDatabaseFactory() = default;

    shared_ptr<PatternDatabase> extract_pdb() {
        return make_shared<PatternDatabase>(
            move(projection),
            move(distances));
    }

    vector<vector<OperatorID>> &&extract_wildcard_plan() {
        return move(wildcard_plan);
    }
};

void PatternDatabaseFactory::compute_variable_to_index(const Pattern &pattern) {
    variable_to_index.resize(variables.size(), -1);
    for (size_t i = 0; i < pattern.size(); ++i) {
        variable_to_index[pattern[i]] = i;
    }
}

AbstractOperator PatternDatabaseFactory::build_abstract_operator(
    const vector<FactPair> &prev_pairs,
    const vector<FactPair> &pre_pairs,
    const vector<FactPair> &eff_pairs,
    int concrete_op_id,
    int cost) const {
    vector<FactPair> regression_preconditions(prev_pairs);
    regression_preconditions.insert(regression_preconditions.end(),
                                    eff_pairs.begin(),
                                    eff_pairs.end());
    // Sort preconditions for MatchTree construction.
    sort(regression_preconditions.begin(), regression_preconditions.end());
    for (size_t i = 1; i < regression_preconditions.size(); ++i) {
        assert(regression_preconditions[i].var !=
               regression_preconditions[i - 1].var);
    }
    int hash_effect = 0;
    assert(pre_pairs.size() == eff_pairs.size());
    for (size_t i = 0; i < pre_pairs.size(); ++i) {
        int var = pre_pairs[i].var;
        assert(var == eff_pairs[i].var);
        int old_val = eff_pairs[i].value;
        int new_val = pre_pairs[i].value;
        assert(new_val != -1);
        int effect = (new_val - old_val) * projection.get_multiplier(var);
        hash_effect += effect;
    }
    return AbstractOperator(concrete_op_id, cost, move(regression_preconditions), hash_effect);
}

void PatternDatabaseFactory::multiply_out(
    int concrete_op_id,
    int cost,
    int pos,
    vector<FactPair> &prev_pairs,
    vector<FactPair> &pre_pairs,
    vector<FactPair> &eff_pairs,
    const vector<FactPair> &effects_without_pre,
    vector<AbstractOperator> &operators) const {
    if (pos == static_cast<int>(effects_without_pre.size())) {
        // All effects without precondition have been checked: insert op.
        if (!eff_pairs.empty()) {
            operators.push_back(
                build_abstract_operator(
                    prev_pairs, pre_pairs, eff_pairs,
                    concrete_op_id, cost));
        }
    } else {
        // For each possible value for the current variable, build an
        // abstract operator.
        int var_id = effects_without_pre[pos].var;
        int eff = effects_without_pre[pos].value;
        VariableProxy var = variables[projection.get_pattern()[var_id]];
        for (int i = 0; i < var.get_domain_size(); ++i) {
            if (i != eff) {
                pre_pairs.emplace_back(var_id, i);
                eff_pairs.emplace_back(var_id, eff);
            } else {
                prev_pairs.emplace_back(var_id, i);
            }
            multiply_out(concrete_op_id, cost,
                         pos + 1, prev_pairs, pre_pairs, eff_pairs,
                         effects_without_pre, operators);
            if (i != eff) {
                pre_pairs.pop_back();
                eff_pairs.pop_back();
            } else {
                prev_pairs.pop_back();
            }
        }
    }
}

void PatternDatabaseFactory::build_abstract_operators_for_op(
    const OperatorProxy &op,
    int cost,
    vector<AbstractOperator> &operators) const {
    // All variable value pairs that are a prevail condition
    vector<FactPair> prev_pairs;
    // All variable value pairs that are a precondition (value != -1)
    vector<FactPair> pre_pairs;
    // All variable value pairs that are an effect
    vector<FactPair> eff_pairs;
    // All variable value pairs that are a precondition (value = -1)
    vector<FactPair> effects_without_pre;

    size_t num_vars = variables.size();
    vector<bool> has_precond_and_effect_on_var(num_vars, false);
    vector<bool> has_precondition_on_var(num_vars, false);

    for (FactProxy pre : op.get_preconditions())
        has_precondition_on_var[pre.get_variable().get_id()] = true;

    for (EffectProxy eff : op.get_effects()) {
        int var_id = eff.get_fact().get_variable().get_id();
        int pattern_var_id = variable_to_index[var_id];
        int val = eff.get_fact().get_value();
        if (pattern_var_id != -1) {
            if (has_precondition_on_var[var_id]) {
                has_precond_and_effect_on_var[var_id] = true;
                eff_pairs.emplace_back(pattern_var_id, val);
            } else {
                effects_without_pre.emplace_back(pattern_var_id, val);
            }
        }
    }
    for (FactProxy pre : op.get_preconditions()) {
        int var_id = pre.get_variable().get_id();
        int pattern_var_id = variable_to_index[var_id];
        int val = pre.get_value();
        if (pattern_var_id != -1) { // variable occurs in pattern
            if (has_precond_and_effect_on_var[var_id]) {
                pre_pairs.emplace_back(pattern_var_id, val);
            } else {
                prev_pairs.emplace_back(pattern_var_id, val);
            }
        }
    }
    multiply_out(op.get_id(), cost, 0,
                 prev_pairs, pre_pairs, eff_pairs, effects_without_pre,
                 operators);
}

void PatternDatabaseFactory::compute_abstract_operators(
    const vector<int> &operator_costs) {
    for (OperatorProxy op : task_proxy.get_operators()) {
        int op_cost;
        if (operator_costs.empty()) {
            op_cost = op.get_cost();
        } else {
            op_cost = operator_costs[op.get_id()];
        }
        build_abstract_operators_for_op(
            op, op_cost, abstract_ops);
    }
}

unique_ptr<MatchTree> PatternDatabaseFactory::compute_match_tree() const {
    unique_ptr<MatchTree> match_tree = utils::make_unique_ptr<MatchTree>(task_proxy, projection);
    for (size_t op_id = 0; op_id < abstract_ops.size(); ++op_id) {
        const AbstractOperator &op = abstract_ops[op_id];
        match_tree->insert(op_id, op.get_regression_preconditions());
    }
    return match_tree;
}

void PatternDatabaseFactory::compute_abstract_goals() {
    for (FactProxy goal : task_proxy.get_goals()) {
        int var_id = goal.get_variable().get_id();
        int val = goal.get_value();
        if (variable_to_index[var_id] != -1) {
            abstract_goals.emplace_back(variable_to_index[var_id], val);
        }
    }
}

bool PatternDatabaseFactory::is_goal_state(int state_index) const {
    for (const FactPair &abstract_goal : abstract_goals) {
        int pattern_var_id = abstract_goal.var;
        int val = projection.unrank(state_index, pattern_var_id);
        if (val != abstract_goal.value) {
            return false;
        }
    }
    return true;
}



void PatternDatabaseFactory::compute_distances(
    const MatchTree &match_tree, bool compute_plan) {
    distances.reserve(projection.get_num_abstract_states());
    // first implicit entry: priority, second entry: index for an abstract state
    priority_queues::AdaptiveQueue<int> pq;

    // initialize queue
    for (int state_index = 0; state_index < projection.get_num_abstract_states(); ++state_index) {
        if (is_goal_state(state_index)) {
            pq.push(0, state_index);
            distances.push_back(0);
        } else {
            distances.push_back(numeric_limits<int>::max());
        }
    }

    if (compute_plan) {
        /*
          If computing a plan during Dijkstra, we store, for each state,
          an operator leading from that state to another state on a
          strongly optimal plan of the PDB. We store the first operator
          encountered during Dijkstra and only update it if the goal distance
          of the state was updated. Note that in the presence of zero-cost
          operators, this does not guarantee that we compute a strongly
          optimal plan because we do not minimize the number of used zero-cost
          operators.
         */
        generating_op_ids.resize(projection.get_num_abstract_states());
    }

    
    //const auto &mutex_map = task_proxy.get_mutex_facts();
    const auto &mutexes = [&]()->std::unordered_map<FactPair, std::vector<FactPair>, utils::FactPairHash>{
        std::unordered_map<FactPair, vector<FactPair>, utils::FactPairHash> map_of_mutex_facts;
       
        lp::LPSolver lp_solver(lp::LPSolverType::CPLEX);
        lp_solver.set_mip_gap(0);
        named_vector::NamedVector<lp::LPVariable> variables;
        named_vector::NamedVector<lp::LPConstraint> constraints;
        named_vector::NamedVector<lp::LPConstraint> exclusion_constraints;
        std::unordered_map<int, int> map_fact_id_to_variable_id;

        const size_t number_of_variables = task_proxy.get_variables().size();
        std::vector<int> compute_fact_id(number_of_variables, 0);
        int total_index = 0;
        
        for(size_t variable_index = 0 ; variable_index < number_of_variables; variable_index++){
            compute_fact_id[variable_index] = total_index;
            total_index += task_proxy.get_variables()[variable_index].get_domain_size();
        }

        std::vector<std::vector<int>> all_solutions;

        const double infinity = lp_solver.get_infinity();
        for(size_t variable_index = 0; variable_index < number_of_variables; variable_index++){
            const VariableProxy &vars = task_proxy.get_variables()[variable_index];
            for(int val = 0; val < vars.get_domain_size(); val++){
                const int fact_id = compute_fact_id[variable_index] + val;
                map_fact_id_to_variable_id.emplace(fact_id,variables.size());
                variables.push_back(lp::LPVariable(0, 1,  1, true));

            }
     
        }

        lp::LPConstraint init_state_constraint(0.0, 1.0);
        for(size_t variable_index = 0; variable_index < number_of_variables; variable_index++){
            int init_val = task_proxy.get_initial_state()[variable_index].get_value();
            int fact_id = compute_fact_id[variable_index] + init_val;
            auto it = map_fact_id_to_variable_id.find(fact_id);
            if(it != map_fact_id_to_variable_id.end()){
                init_state_constraint.insert(it->second, 1.0);    

            }
            
        }

        constraints.push_back(std::move(init_state_constraint));

        for(const OperatorProxy &op : task_proxy.get_operators()){
            lp::LPConstraint action_constraint(-infinity, 0.0);

            for(const EffectProxy &effect : op.get_effects()){
                const FactProxy affected_fact = effect.get_fact();
                const int variable_index = affected_fact.get_variable().get_id();
                if(variable_index < 0 || static_cast<size_t>(variable_index) >= number_of_variables) continue;
                const int value = affected_fact.get_value();
                const int fact_id = compute_fact_id[variable_index] + value;
                auto it = map_fact_id_to_variable_id.find(fact_id);
                if(it != map_fact_id_to_variable_id.end()){
                    action_constraint.insert(it->second, 1.0);
                }

            }

            for(const FactProxy &precond : op.get_preconditions()){
                int variable_index = precond.get_variable().get_id();
                if(variable_index < 0 || static_cast<size_t>(variable_index) >= number_of_variables) continue;
                int value = precond.get_value();
                int fact_id = compute_fact_id[variable_index] + value;
                auto precond_iter = map_fact_id_to_variable_id.find(fact_id);
                if(precond_iter != map_fact_id_to_variable_id.end()){
                    for(const EffectProxy &effect : op.get_effects()){
                        const FactProxy deleted_fact = effect.get_fact();
                        if(deleted_fact.get_variable().get_id() == precond.get_variable().get_id() && deleted_fact.get_value() != precond.get_value()){
                            const int delete_fact_id = compute_fact_id[variable_index] + deleted_fact.get_value();
                            auto delete_iter = map_fact_id_to_variable_id.find(delete_fact_id);
                            if(delete_iter != map_fact_id_to_variable_id.end()){
                                action_constraint.insert(precond_iter->second, -1.0);
                            }
                        }
                    }
                }

            }
            constraints.push_back(std::move(action_constraint));

        }
        lp::LinearProgram lp (lp::LPObjectiveSense::MAXIMIZE, std::move(variables), std::move(constraints), infinity);
        lp_solver.load_problem(lp);
        lp_solver.solve();
        
        while(lp_solver.has_optimal_solution() && lp_solver.get_objective_value() > 1.5){
            auto solution_set = lp_solver.extract_solution();

            if (solution_set.empty()) break;
            
            std::vector<int> current_solution;
            current_solution.reserve(solution_set.size());
            for(size_t i = 0; i < solution_set.size(); i++ ){
                if(solution_set[i] > 0.5){
                    current_solution.push_back(i);
                    }
                }
            all_solutions.push_back(current_solution);
    
            lp::LPConstraint exclusion_constraint(1.0, infinity);
            for(size_t i = 0; i < solution_set.size(); i++){
                if(solution_set[i] <= 0.5){
                    exclusion_constraint.insert(i, 1.0);
                }
            }
            
            exclusion_constraints.push_back(std::move(exclusion_constraint));
            lp_solver.clear_temporary_constraints();
            lp_solver.add_temporary_constraints(exclusion_constraints);
            
            lp_solver.solve();

        }
        
        
        
        std::unordered_map<int, FactPair>reverse_map_LP_variable_id_to_FactPair;
        for(const auto &i : map_fact_id_to_variable_id){
            int fact_id = i.first;
            int lp_variable_id = i.second;
            int var   = -1;
            int value = -1;
            for(size_t variable_id = 0; variable_id < compute_fact_id.size(); variable_id++){
                int init_fact_id = compute_fact_id[variable_id];
                if(fact_id >= init_fact_id && fact_id < init_fact_id + task_proxy.get_variables()[variable_id].get_domain_size()){
                    var = variable_id;
                    value = fact_id - init_fact_id;
                    break;
                }
            }
            if(var != -1 && value != -1){
                reverse_map_LP_variable_id_to_FactPair.emplace(lp_variable_id , FactPair(var,value));
            }
        }

        std::vector<std::unordered_set<int>> related_LP_variables(reverse_map_LP_variable_id_to_FactPair.size());
        for(const auto &solution : all_solutions){
            for(int var1 : solution){
                if(var1 >= 0 && static_cast<size_t>(var1)< related_LP_variables.size()){
                    for(int var2 : solution){
                        if(var2 >= 0 && static_cast<size_t>(var2)< related_LP_variables.size() && var1 != var2){
                            related_LP_variables[var1].insert(var2);
                            related_LP_variables[var2].insert(var1);
                        }
                    }
                }
                
            }
        }

        for(const auto &i : reverse_map_LP_variable_id_to_FactPair){
            int lp_variable = i.first;
            FactPair fact = i.second;

            std::vector<FactPair> mutex_facts;
            mutex_facts.reserve(reverse_map_LP_variable_id_to_FactPair.size());
            if(lp_variable >= 0 && static_cast<size_t>(lp_variable)< related_LP_variables.size()){
                for(const auto &mutex_value : reverse_map_LP_variable_id_to_FactPair){
                    int mutex_lp_variable = mutex_value.first;
                    FactPair mutex_fact = mutex_value.second;

                    if(lp_variable != mutex_lp_variable && related_LP_variables[lp_variable].find(mutex_lp_variable) != related_LP_variables[lp_variable].end()){
                        mutex_facts.push_back(mutex_fact);
                    }
                }
            }
            
            if(!mutex_facts.empty()){
                map_of_mutex_facts[fact] = std::move(mutex_facts);
            }
            
        }
        return map_of_mutex_facts;
    }();
    vector<int> global_variable_to_pattern_id(task_proxy.get_variables().size(),-1);
            for(size_t i = 0; i < projection.get_pattern().size(); i++){
                global_variable_to_pattern_id[projection.get_pattern()[i]]=i;
            }
            
    vector<FactPair> preconditions; 
    preconditions.reserve(task_proxy.get_variables().size());

    utils::HashMap<pair<int, int>, int> unranked_cache_value;

    // Dijkstra loop
    std::cout << mutexes.size() << endl;
    while (!pq.empty()) {
        pair<int, int> node = pq.pop();
        int distance = node.first;
        int state_index = node.second;
        if (distance > distances[state_index]) {
            continue;
        }

        // regress abstract_state
        vector<int> applicable_operator_ids;
        match_tree.get_applicable_operator_ids(state_index, applicable_operator_ids);
        for (int op_id : applicable_operator_ids) {
            const AbstractOperator &op = abstract_ops[op_id];
            int predecessor = state_index + op.get_hash_effect();

            int concrete_operator_id = op.get_concrete_op_id();
            const OperatorProxy &concrete_operator = task_proxy.get_operators()[concrete_operator_id];

            preconditions.clear(); 
            for (FactProxy precond : concrete_operator.get_preconditions()) {
                preconditions.push_back(precond.get_pair());
            }
    
            bool mutex_violation_found = false;

            for(const auto &pair_of_mutex_facts: mutexes){

                const FactPair &fact = pair_of_mutex_facts.first;//check if in precond
                const vector<FactPair> &mutex_facts = pair_of_mutex_facts.second;
 
                int fact_pattern_id = global_variable_to_pattern_id[fact.var];


                bool is_fact_in_precondition = false;
                for(const FactPair precondition : preconditions){
                    if(precondition.var == fact.var && precondition.value == fact.value){
                        is_fact_in_precondition = true;
                        break;
                    }  
                }
               

                bool is_fact_in_pattern = false;
                if(fact_pattern_id != -1){
                    auto iter = unranked_cache_value.find(std::make_pair(fact_pattern_id,predecessor));
                    if(iter != unranked_cache_value.end()){
                        is_fact_in_pattern = (iter->second == fact.value);
                    } 
                    else{
                        int unranked_val = projection.unrank(predecessor,fact_pattern_id);
                        unranked_cache_value.emplace(std::make_pair(fact_pattern_id, predecessor), unranked_val);
                        is_fact_in_pattern = (unranked_val == fact.value);
                    }
                }

                if(!is_fact_in_pattern && !is_fact_in_precondition){
                    continue;
                }
                     
                for(const FactPair &mutex_fact : mutex_facts){
                    
                    int pattern_id = global_variable_to_pattern_id[mutex_fact.var];
                    
                    bool is_mutex_fact_in_precondition = false;

                    for(const FactPair precond: preconditions){

                        if(precond.var == mutex_fact.var && precond.value == mutex_fact.value){
                            is_mutex_fact_in_precondition = true;
                            break;

                        }

                    }
                    
                    
                    bool is_mutex_fact_in_state = false;

                    if(pattern_id != -1){
                        auto iter = unranked_cache_value.find(std::make_pair(pattern_id,predecessor));
                        if(iter != unranked_cache_value.end()){
                            is_mutex_fact_in_state = (iter->second == mutex_fact.value);
                        } 
                        else{
                            int state_unranked_val = projection.unrank(predecessor,pattern_id);
                            unranked_cache_value.emplace(std::make_pair(pattern_id, predecessor), state_unranked_val);
                            is_mutex_fact_in_state = (state_unranked_val == mutex_fact.value);
                        }
                    }
                    if(is_mutex_fact_in_state || is_mutex_fact_in_precondition ){
                        mutex_violation_found = true;
                        break;
                        
                    }
                    
                    if(mutex_violation_found){  
                        break;
                   } 

                }
                

            }
            if(!mutex_violation_found){
                        int alternative_cost = distances[state_index] + op.get_cost();
                        if (alternative_cost < distances[predecessor]) {
                            distances[predecessor] = alternative_cost;
                            pq.push(alternative_cost, predecessor);
                            if (compute_plan) {
                                generating_op_ids[predecessor] = op_id;
                            }
                        }
                    }
            
        }
    }
}

void PatternDatabaseFactory::compute_plan(
    const MatchTree &match_tree,
    const shared_ptr<utils::RandomNumberGenerator> &rng,
    bool compute_wildcard_plan) {
    /*
      Using the generating operators computed during Dijkstra, we start
      from the initial state and follow the generating operator to the
      next state. Then we compute all operators of the same cost inducing
      the same abstract transition and randomly pick one of them to
      set for the next state. We iterate until reaching a goal state.
      Note that this kind of plan extraction does not uniformly at random
      consider all successor of a state but rather uses the arbitrarily
      chosen generating operator to settle on one successor state, which
      is biased by the number of operators leading to the same successor
      from the given state.
    */
    State initial_state = task_proxy.get_initial_state();
    initial_state.unpack();
    int current_state =
        projection.rank(initial_state.get_unpacked_values());
    if (distances[current_state] != numeric_limits<int>::max()) {
        while (!is_goal_state(current_state)) {
            int op_id = generating_op_ids[current_state];
            assert(op_id != -1);
            const AbstractOperator &op = abstract_ops[op_id];
            int successor_state = current_state - op.get_hash_effect();

            // Compute equivalent ops
            vector<OperatorID> cheapest_operators;
            vector<int> applicable_operator_ids;
            match_tree.get_applicable_operator_ids(successor_state, applicable_operator_ids);
            for (int applicable_op_id : applicable_operator_ids) {
                const AbstractOperator &applicable_op = abstract_ops[applicable_op_id];
                int predecessor = successor_state + applicable_op.get_hash_effect();
                if (predecessor == current_state && op.get_cost() == applicable_op.get_cost()) {
                    cheapest_operators.emplace_back(applicable_op.get_concrete_op_id());
                }
            }
            if (compute_wildcard_plan) {
                rng->shuffle(cheapest_operators);
                wildcard_plan.push_back(move(cheapest_operators));
            } else {
                OperatorID random_op_id = *rng->choose(cheapest_operators);
                wildcard_plan.emplace_back();
                wildcard_plan.back().push_back(random_op_id);
            }

            current_state = successor_state;
        }
    }
    utils::release_vector_memory(generating_op_ids);
}



/*
  Note: if we move towards computing PDBs via command line option, e.g. as
  in pdb_heuristic(pdb(pattern=...)), then this class might become a builder
  class for pattern databases.
*/
PatternDatabaseFactory::PatternDatabaseFactory(
    const TaskProxy &task_proxy,
    const Pattern &pattern,
    const vector<int> &operator_costs,
    bool compute_plan,
    const shared_ptr<utils::RandomNumberGenerator> &rng,
    bool compute_wildcard_plan)
    : task_proxy(task_proxy),
      variables(task_proxy.get_variables()),
      projection(task_proxy, pattern) {
    assert(operator_costs.empty() ||
           operator_costs.size() == task_proxy.get_operators().size());
    compute_variable_to_index(pattern);
    compute_abstract_operators(operator_costs);
    unique_ptr<MatchTree> match_tree = compute_match_tree();
    compute_abstract_goals();
    compute_distances(*match_tree, compute_plan);

    if (compute_plan) {
        this->compute_plan(*match_tree, rng, compute_wildcard_plan);
    }
}

shared_ptr<PatternDatabase> compute_pdb(
    const TaskProxy &task_proxy,
    const Pattern &pattern,
    const vector<int> &operator_costs,
    const shared_ptr<utils::RandomNumberGenerator> &rng) {
    task_proxy.get_mutex_facts();
    PatternDatabaseFactory pdb_factory(task_proxy, pattern, operator_costs, false, rng);
    return pdb_factory.extract_pdb();
}

tuple<shared_ptr<PatternDatabase>, vector<vector<OperatorID>>>
compute_pdb_and_plan(
    const TaskProxy &task_proxy,
    const Pattern &pattern,
    const vector<int> &operator_costs,
    const shared_ptr<utils::RandomNumberGenerator> &rng,
    bool compute_wildcard_plan) {
    PatternDatabaseFactory pdb_factory(task_proxy, pattern, operator_costs, true, rng, compute_wildcard_plan);
    return {pdb_factory.extract_pdb(), pdb_factory.extract_wildcard_plan()};
}
}