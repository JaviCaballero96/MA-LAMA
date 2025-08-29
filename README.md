# MA-LAMA
- Caballero Testón, J., & R-Moreno, M. D. (2024). Multi-Agent Temporal Task Solving and Plan Optimization. Proceedings of the International Conference on Automated Planning and Scheduling, 34(1), 50-58. https://doi.org/10.1609/icaps.v34i1.31460
- J. Caballero Testón and Maria D. R-Moreno. 2025. MA-LAMA: Exploiting the Multi-Agent Nature of Temporal PlanningProblems.Journal of Artificial Intelligence Research83, Article 23 (August 2025), 41 pages.doi: https://doi.org/10.1613/jair.1.18906

## --- If you want to use MA-LAMA ---

Then you just need the utils/MA-LAMA_Deploy.sh script.
Just execute in a clean directory, it will download all modules and compile the ones coded in C++. Then MA-LAMA can be launched by executing the command: 
### launchLama.sh domain_file problem_file time_relaxed_search(s) agent_decomp?(y/n) launch_hard_temp_constraints?(h)

The final plan is stored as final_plan.txt

## --- If you want to develop over the MA-LAMA translate module ---

This project composes the phase ONE of the MA-LAMA planner, it is only meant to be downloaded separately for developement purposes.
This phase aims to build a complete translator from temporal pddl2.1 to SAS+ tasks (inherited from the LAMA planner). Additionally, it also comprises the Agent Decomposition and Goal Classification and Assignment algoriothms, that divide the full task into local problems and assign the goals in terms of cost optimization.

To launch:

python3 translate.py domain.pddl problem.pddl agent_local_relaxed_search_time agent_decomp?(y/n)

The translator generates the following files in its root directory:
  - agent[n_agent].groups: one for each task agent found, contains the variables(invariants) definition of each agent.
  - output.sas: contains the full task metric, variables, initial state, shared variables, goals and operators.
  - test.groups: contains the full task variables(invariants).
  - all.groups: contains the full task variables(invariants).

Additionally, it generates one folder <step_[n_SearchStep]> for each Search Step, which contains the following files:
  - output_agent[n_agent].sas: one for each agent that particiapes in the Search Phase, contains each agent metric, variables, initial state, shared variables, goals and operators.
