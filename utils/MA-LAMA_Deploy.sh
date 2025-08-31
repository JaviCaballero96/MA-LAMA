#/bin/bash

echo "LAMA_Magent is going to be deployed :)"
sleep 2
echo "Downloading all modules from git..."

echo "  translate..."
git clone -b GMV https://github.com/JaviCaballero96/MA-LAMA.git
cp MA-LAMA/utils/* .
mv MA-LAMA translate
chmod -R +x translate/*
chmod +x launchMALama.sh

echo "  preprocess..."
git clone -b GMV https://github.com/JaviCaballero96/MA-LAMA_preprocess.git
mv MA-LAMA_preprocess/preprocess preprocess
rm -rf MA-LAMA_preprocess

echo "  search..."
git clone -b GMV https://github.com/JaviCaballero96/MA-LAMA_search.git
mv MA-LAMA_search/search search
rm -rf MA-LAMA_search

echo "  unify..."
git clone -b GMV https://github.com/JaviCaballero96/MA-LAMA_unify.git
mv MA-LAMA_unify unify
chmod -R +x unify

mkdir graphs
mkdir graphs/metric
mkdir graphs/functional_graphs_inv

echo ""
echo "----------------------------------------------------------"
echo "All modules are now downloaded, preprocess and search need to be compiled..."
echo "----------------------------------------------------------"
echo ""
echo "  compiling preprocess..."
echo ""

cd preprocess
mkdir obj
make clean
make
chmod +x preprocess
cd ..

echo ""
echo "  compiling search..."
echo ""
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
echo "Usage: launchMALama.sh domain_file problem_file relaxed_search_time agent_decomp?(y/n)"
echo "Output: final_plan.txt, see Readme.txt for a full description of all outputs."
