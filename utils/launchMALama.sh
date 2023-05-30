#bin/bash

echo "Usage: launchLama.sh domain_file problem_file"

echo "removing past files"
rm -f agent*.groups
rm -f all.groups
rm -f final_plan.txt
rm -f output*
rm -f test.groups
rm -f *.log

echo "Launching Translate"
python3 pddl2-SAS-translate/translate.py $1 $2 > translate.log

echo "Launching Preprocess"
for file in output_agent*.sas
do
	echo "Launching preprocess for $file"
	preprocess/preprocess $file >> prepros.log
done

echo "Launching search"
for file in output_preproagent*
do
	echo "Launching search for $file"
	timeout 5s search/search wli $file >> searchs.log
done

echo "Launching unify"
python3 unify_temp_magent/main.py > unify.log

echo "end"
