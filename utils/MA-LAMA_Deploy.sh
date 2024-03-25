#/bin/bash

echo "LAMA_Magent is going to be deployed :)"
sleep 2
echo "Downloading all modules from git..."

echo "  translate..."
gh repo clone JaviCaballero96/pddl2-SAS-translate
cp pddl2-SAS-translate/utils/* .
chmod -R +x pddl2-SAS-translate/*
chmod +x launchLama.sh

echo "  preprocess..."
gh repo clone JaviCaballero96/preprocess_temp_magent
mv preprocess_temp_magent/preprocess preprocess
rm -rf preprocess_temp_magent

echo "  search..."
gh repo clone JaviCaballero96/search_temp_magent
mv search_temp_magent/search search
rm -rf search_temp_magent

echo "  unify..."
gh repo clone JaviCaballero96/unify_temp_magent
chmod -R +x unify_temp_magent/*

mkdir graphs
mkdir graphs/metric
mkdir graphs/functional_graphs_inv

echo "All modules are now downloaded, preprocess and search need to be compiled..."
echo "  compiling preprocess..."
cd preprocess
mkdir obj
make clean
make
chmod +x preprocess
cd ..

echo "  compiling search..."
cd search
mkdir obj
make clean
make
chmod +x search
cd ..

echo ""
echo ""
echo "---- Deploy completed!! ----"
echo ""
echo ""
echo "Usage: launchLama.sh domain_file problem_file relaxed_search_time agent_decomp?(y/n)"
echo "Output: final_plan.txt, see Readme.txt for a full description of all outputs."