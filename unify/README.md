
## --- If you want to use MA-LAMA, please refer to the MA-LAMA repository ---

This project composes the phase FOUR of the MA-LAMA planner, it is only meant to be downloaded separately for developement purposes.
More precisely, this module assembles all the partial plans generated in each Search phase execution and generates the final temporal plan.

To launch, it takes as an input the output.sas file(s) from the preprocess module and the all.groups from the translate module:

python3 main.py

Reads internally as an input every solution (agnet_[n_agnet].[n_found_solution]) generated in the step_[SearchPhase] folders for eeach agent by the Search module.

Generates in the root directory the final_plan.txt assembled temporal final solution.

