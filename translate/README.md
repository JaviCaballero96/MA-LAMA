This project composes the phase ONE of the MA-LAMA planner.
This phase aims to build a complete translator from temporal pddl2.1 to SAS+ tasks (inherited from the LAMA planner). Additionally, it also comprises the Agent Decomposition and Goal Classification and Assignment algoriothms, that divide the full task into local problems and assign the goals in terms of cost optimization.

To launch:

python3 translate.py domain.pddl problem.pddl agent_local_relaxed_search_time agent_decomp?(y/n)

The translator generates the following files in its root directory:
  - agent[n_agent].groups: one for each task agent found, contains the variables(invariants) definition of each agent.
  - output.sas: contains the full task metric, variables, initial state, shared variables, goals and operators.
  - test.groups: contains the full task variables(invariants).
  - all.groups: contains the full task variables(invariants).

Additionally, it generates one folder <step_[n_SearchPhase]> for each Search Phase, which contains the following files:
  - output_agent[n_agent].sas: one for each agent that particiapes in the Search Phase, contains each agent metric, variables, initial state, shared variables, goals and operators.
