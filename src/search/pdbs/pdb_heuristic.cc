#include "pdb_heuristic.h"

#include "pattern_database.h"

#include "../plugins/plugin.h"
#include "../utils/markup.h"

#include <limits>
#include <memory>

using namespace std;

namespace pdbs {
static shared_ptr<PatternDatabase> get_pdb_from_generator(
    const shared_ptr<AbstractTask> &task,
    const shared_ptr<PatternGenerator> &pattern_generator) {
    PatternInformation pattern_info = pattern_generator->generate(task);
    return pattern_info.get_pdb();
}

PDBHeuristic::PDBHeuristic(
    const shared_ptr<PatternGenerator> &pattern,
    const shared_ptr<AbstractTask> &transform, bool cache_estimates,
    const string &description, utils::Verbosity verbosity)
    : Heuristic(transform, cache_estimates, description, verbosity),
      pdb(get_pdb_from_generator(task, pattern)),
      lp_solver(lp::LPSolverType::CPLEX) {
        lp_solver.set_mip_gap(0);
        named_vector::NamedVector<lp::LPVariable> variables;
        named_vector::NamedVector<lp::LPConstraint> constraints;

        std::unordered_map<int, int> map_fact_id_to_variable;

        std::vector<int> compute_fact_id(task_proxy.get_variables().size(), 0);
        int total_index = 0;
        for(size_t variable_index = 0 ; variable_index < task_proxy.get_variables().size(); variable_index++){
            compute_fact_id[variable_index] = total_index;
            total_index += task_proxy.get_variables()[variable_index].get_domain_size();
        }
        

        double infinity = lp_solver.get_infinity();
        for(size_t variable_index = 0; variable_index < task_proxy.get_variables().size(); variable_index++){
            VariableProxy vars = task_proxy.get_variables()[variable_index];
            for(int val = 0; val < vars.get_domain_size(); val++){
                int fact_id = compute_fact_id[variable_index] + val;
                map_fact_id_to_variable[fact_id] = variables.size();
                variables.push_back(lp::LPVariable(0, 1,  1, true));

                std::cout << "Fact ID: " << fact_id << ", Variable ID: " << map_fact_id_to_variable[fact_id] << std::endl;

            }
     
        }

        lp::LPConstraint init_state_constraint(0.0,1.0);
        for(size_t variable_index = 0; variable_index < task_proxy.get_variables().size(); variable_index++){
            int init_val = task_proxy.get_initial_state()[variable_index].get_value();
            int fact_id = compute_fact_id[variable_index] + init_val;
            auto it = map_fact_id_to_variable.find(fact_id);
            if(it != map_fact_id_to_variable.end()){
                init_state_constraint.insert(it->second,1.0);    

                std::cout << "Initial State - Fact ID: " << fact_id << ", Variable ID: " << it->second << std::endl;
            }
            
        }

        constraints.push_back(init_state_constraint);

        for(OperatorProxy op : task_proxy.get_operators()){
            lp::LPConstraint action_constraint(-infinity, 0.0);

            for(EffectProxy effect : op.get_effects()){
                FactProxy affected_fact = effect.get_fact();
                int variable_index = affected_fact.get_variable().get_id();
                int value = affected_fact.get_value();
                int fact_id = compute_fact_id[variable_index] + value;
                auto it = map_fact_id_to_variable.find(fact_id);
                if(it != map_fact_id_to_variable.end()){
                    action_constraint.insert(it->second,1.0);
                    std::cout << "Operator Effect - Fact ID: " << fact_id << ", Variable ID: " << it->second << std::endl;
                }

            }
        }




        lp::LinearProgram lp (lp::LPObjectiveSense::MAXIMIZE, move(variables), move(constraints), infinity);
        lp_solver.load_problem(lp);

}

int PDBHeuristic::compute_heuristic(const State &ancestor_state) {
    State state = convert_ancestor_state(ancestor_state);
    int h = pdb->get_value(state.get_unpacked_values());
    if (h == numeric_limits<int>::max())
        return DEAD_END;
    return h;
}

static basic_string<char> paper_references() {
    return utils::format_conference_reference(
        {"Stefan Edelkamp"},
        "Planning with Pattern Databases",
        "https://aaai.org/papers/7280-ecp-01-2001/",
        "Proceedings of the Sixth European Conference on Planning (ECP 2001)",
        "84-90",
        "AAAI Press",
        "2001") +
           "For implementation notes, see:" + utils::format_conference_reference(
        {"Silvan Sievers", "Manuela Ortlieb", "Malte Helmert"},
        "Efficient Implementation of Pattern Database Heuristics for"
        " Classical Planning",
        "https://ai.dmi.unibas.ch/papers/sievers-et-al-socs2012.pdf",
        "Proceedings of the Fifth Annual Symposium on Combinatorial"
        " Search (SoCS 2012)",
        "105-111",
        "AAAI Press",
        "2012");
}
class PDBHeuristicFeature
    : public plugins::TypedFeature<Evaluator, PDBHeuristic> {
public:
    PDBHeuristicFeature() : TypedFeature("pdb") {
        document_subcategory("heuristics_pdb");
        document_title("Pattern database heuristic");
        document_synopsis(
            "Computes goal distance in "
            "state space abstractions based on projections. "
            "First used in domain-independent planning by:"
            + paper_references());

        add_option<shared_ptr<PatternGenerator>>(
            "pattern",
            "pattern generation method",
            "greedy()");
        add_heuristic_options_to_feature(*this, "pdb");

        document_language_support("action costs", "supported");
        document_language_support("conditional effects", "not supported");
        document_language_support("axioms", "not supported");

        document_property("admissible", "yes");
        document_property("consistent", "yes");
        document_property("safe", "yes");
        document_property("preferred operators", "no");
    }

    virtual shared_ptr<PDBHeuristic> create_component(
        const plugins::Options &opts,
        const utils::Context &) const override {
        return plugins::make_shared_from_arg_tuples<PDBHeuristic>(
            opts.get<shared_ptr<PatternGenerator>>("pattern"),
            get_heuristic_arguments_from_options(opts)
            );
    }
};

static plugins::FeaturePlugin<PDBHeuristicFeature> _plugin;
}
