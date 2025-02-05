#bin/bash

echo "Usage: launchLama.sh domain_file problem_file time_relaxed_search(s) timed_goal_assigment(y/n)"

echo "removing past files"
rm -rf step_*
rm -f end_state
rm -f current_constraints
rm -f agent*.groups
rm -f all.groups
rm -f final_plan.txt
rm -f GMV*.txt
rm -f output.sas
rm -f all.groups
rm -f test.groups
rm -f *.log
rm -f plan_*.txt
rm -f unify_info.txt



start=`date +%s.%N`

echo "Launching with SOFT temporal constraints"

echo "Launching Translate"
python3 translate/translate.py $1 $2 $3 y $4 > translate.log

echo "Launching Preprocess"
folder=step_0

files_dir_prepro="step_0/"output_agent*.sas
echo "Preprocess and search will be launched for step_0"
for file in $files_dir_prepro
do
	echo "Launching preprocess for $file"
	preprocess/preprocess $file >> prepros.log
done

command="mv output_preproagent* $folder"
`$command`

files_dir_search="step_0/"output_preproagent*
n_search=0
for file in $files_dir_search
do
	if [ "0" -eq "$n_search" ]; then
		echo "Launching search WITHOUT constraints WITHOUT init state for $file"
		timeout 1s search/search wilF $file >> search_"$folder"_"$n_search"_l.log

		FILE=step_0/output_preproagent0.p1
	    if test -f "$FILE"; then
	        echo "Solution found!!"
	    else
	        echo "No solution found, trying FF heuristic."
	        timeout 1s search/search wifF $file >> search_"$folder"_"$n_search"_f.log

	        FILE=step_0/output_preproagent0.p1
	        if test -f "$FILE"; then
	            echo "Solution found!!"
	        else
	            echo "No solution found, trying long landmark heuristic."
	            timeout 10s search/search wilF $file >> search_"$folder"_"$n_search"_l_long.log

			          FILE="$folder/"output_preproagent$n_search.1
	        	if test -f "$FILE"; then
	                echo "Solution found!!"
	            else
	                echo "No solution found, trying long FF heuristic."
	                timeout 10s search/search wifF $file >> search_"$folder"_"$n_search"_f_long.log
	            fi
	        fi
	    fi
	else
		echo "Launching search WITH constraints WITHOUT init state for $file"
		timeout 1s search/search wlF $file >> search_"$folder"_"$n_search"_l.log

		FILE=step_0/output_preproagent"$n_search".p1
	    if test -f "$FILE"; then
	        echo "Solution found!!"
	    else
	        echo "No solution found, trying FF heuristic WITH constraints."
	        timeout 1s search/search wfF $file >> search_"$folder"_"$n_search"_f.log

	        FILE=step_0/output_preproagent0.p1
	        if test -f "$FILE"; then
	            echo "Solution found!!"
	        else
	            echo "No solution found, trying long landmark heuristic WITH constraints."
	            timeout 10s search/search wlF $file >> search_"$folder"_"$n_search"_l_long.log

			          FILE="$folder/"output_preproagent$n_search.p1
	        	if test -f "$FILE"; then
	                echo "Solution found!!"
	            else
	                echo "No solution found, trying long FF heuristic WITH constraints."
	                timeout 10s search/search wfF $file >> search_"$folder"_"$n_search"_f_long.log
	            fi
	        fi
	    fi
    fi
n_search=`expr $n_search + 1`
done

echo "Launching unify"
python3 unify/main.py > unify.log

end=`date +%s.%N`

runtime=$( echo "$end - $start" | bc -l )

grep Expanded step_*/*
grep Cost step*/*
grep "Search time" step*/*
grep Cost final_plan.txt
grep Makespan final_plan.txt

echo "Time spent: $runtime"

echo "end"
