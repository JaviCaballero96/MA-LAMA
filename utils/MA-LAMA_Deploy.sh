#/bin/bash

echo "LAMA_Magent is going to be deployed :)"
sleep 2
echo "Downloading all modules from git..."

echo "  translate..."
gh repo clone JaviCaballero96/MA-LAMA
cp MA-LAMA/utils/* .
mv MA-LAMA translate
chmod -R +x MA-LAMA/*
chmod +x launchLama.sh

echo "  preprocess..."
gh repo clone MA-LAMA_preprocess
mv MA-LAMA_preprocess/preprocess preprocess
rm -rf MA-LAMA_preprocess

echo "  search..."
gh repo clone MA-LAMA_search
mv MA-LAMA_search/search search
rm -rf MA-LAMA_search

echo "  unify..."
gh repo clone MA-LAMA_unify
mv -rf MA-LAMA_unify unify
chmod -R +x MA-LAMA_unify/*

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
