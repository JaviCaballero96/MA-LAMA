#bin/bash

echo "Usage: launchLama.sh domain_file problem_file time_search (h)"

echo "removing past files"
rm -rf step_*
rm -f end_state
rm -f current_constraints
rm -f agent*.groups
rm -f all.groups
rm -f final_plan.txt
rm -f output.sas
rm -f all.groups
rm -f test.groups
rm -f *.log

if [ "$4" = "h" ]; then
  echo "Launching with HARD temporal constraints"
  HARD_CONST=h
else
  echo "Launching with SOFT temporal constraints"
fi

echo "Launching Translate"
python3 pddl2-SAS-translate/translate.py $1 $2 $3> translate.log

echo "Launching Preprocess"
for folder in step_*
do
	if [ "step_0" = "$folder" ]; then
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
				timeout 10s search/search wlFi $file >> search_"$folder"_"$n_search"_l.log

				FILE=step_0/output_preproagent0.1
				if test -f "$FILE"; then
				    echo "Solution found!!"
				else
				    echo "No solution found, trying FF heuristic."
				    timeout 10s search/search wfFi $file >> search_"$folder"_"$n_search"_f.log
				fi

			else
				echo "Launching search WITH constraints WITHOUT init state for $file"
				timeout 10s search/search cwlFi$HARD_CONST $file >> search_"$folder"_"$n_search"_l.log
				FILE="$folder/"output_preproagent$n_search.1
                                if test -f "$FILE"; then
				    echo "Solution found!!"
				else
            echo "No solution found, trying FF heuristic."
	          timeout 10s search/search cwfFi$HARD_CONST $file >> search_"$folder"_"$n_search"_f.log
				fi
			fi
			n_search=`expr $n_search + 1`
		done
	else
		echo "Preprocess and search will be launched for "$folder
		files_dir_search="$folder/"*output*.sas
		for file in $files_dir_search
		do
			echo "Launching preprocess for $file"
			preprocess/preprocess $file >> prepros.log
		done

		command="mv *output_prepro* $folder"
		`$command`

		files_dir_search="$folder/"*output_prepro*
		for file in $files_dir_search
		do
			echo "Launching search WITHOUT constraints WITH init state for $file"
			timeout 10s search/search swlFi $file >> search_"$folder"_l.log

			FILE=$file.1
			if test -f "$FILE"; then
			    echo "Solution found!!!"
			else
          echo "No solution found, trying FF heuristic."
          timeout 10s search/search cwfFi $file >> search_"$folder"_f.log
      fi
		done
	fi
done

echo "Launching unify"
python3 unify_temp_magent/main.py > unify.log

echo "end"
