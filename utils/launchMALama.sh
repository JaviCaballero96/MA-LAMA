#bin/bash

echo "Usage: launchLama.sh domain_file problem_file time_search"

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

echo "Launching Translate"
python3 pddl2-SAS-translate/translate.py $1 $2 $3> translate.log

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
				timeout 15s search/search wlFi $file >> search_"$folder"_"$n_search".log
			else
				echo "Launching search WITH constraints WITHOUT init state for $file"
				timeout 25s search/search cwlFi $file >> search_"$folder"_"$n_search".log
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
			timeout 10s search/search swlFi $file >> search_"$folder"_"$n_search".log
		done
	fi
done

echo "Launching unify"
python3 unify_temp_magent/main.py > unify.log

echo "end"
