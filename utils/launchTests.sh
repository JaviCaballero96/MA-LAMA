#!/bin/bash

echo "Usage: launchTests.sh domain_file problem_file_name(without number) time_each_search(s/m/h) "

pName=$2
time=$3
echo "We will spend $time each search."

rm -rf popcorn result tfd tflap optic MA-LAMA

mkdir result
cp -rf /home/javier/Desktop/planners/ICAPS_24_planners/popcorn .
cp -rf /home/javier/Desktop/planners/ICAPS_24_planners/tfd .
cp -rf /home/javier/Desktop/planners/ICAPS_24_planners/tflap .
mkdir optic
cp -f /home/javier/Desktop/planners/ICAPS_24_planners/optic-clp_exe optic
cp -rf /home/javier/Desktop/planners/LAMA_simlinks MA-LAMA
cd result

# Launch MA-LAMA
mkdir MA-LAMA
cd MA-LAMA
for problem in ../../$pName[0-9]
do
  problemN="$(basename $problem)"
  echo $problemN MA-LAMA
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../MA-LAMA/pddl2-SAS-translate pddl2-SAS-translate
  ln -sfn ../../../MA-LAMA/preprocess preprocess
  ln -sfn ../../../MA-LAMA/search search
  ln -sfn ../../../MA-LAMA/unify_temp_magent unify_temp_magent
  ln -sfn ../../../MA-LAMA/launchMALama.sh launchMALama.sh
  mkdir graphs

  ./launchMALama.sh ../../../$1 ../../../$problemN 3 >> MA-LAMA.log 2>> MA-LAMA.log

  cd ..
done
for problem in ../../$pName[0-9][0-9]
do
  problemN="$(basename $problem)"
  echo $problemN MA-LAMA
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../MA-LAMA/pddl2-SAS-translate pddl2-SAS-translate
  ln -sfn ../../../MA-LAMA/preprocess preprocess
  ln -sfn ../../../MA-LAMA/search search
  ln -sfn ../../../MA-LAMA/unify_temp_magent unify_temp_magent
  ln -sfn ../../../MA-LAMA/launchMALama.sh launchMALama.sh
  mkdir graphs

  ./launchMALama.sh ../../../$1 ../../../$problemN 3 >> MA-LAMA.log 2>> MA-LAMA.log

  cd ..
done
cd ..

# Launch Optic
mkdir optic
cd optic
for problem in ../../$pName[0-9]
do
  problemN="$(basename $problem)"
  echo $problemN OPTIC
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../optic/optic-clp_exe optic-clp_exe

  timeout ${time} ./optic-clp_exe ../../../$1 ../../../$problemN >> OPTIC.log 2>> OPTIC.log

  cd ..
done
for problem in ../../$pName[0-9][0-9]
do
  problemN="$(basename $problem)"
  echo $problemN OPTIC
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../optic/optic-clp_exe optic-clp_exe

  timeout ${time} ./optic-clp_exe ../../../$1 ../../../$problemN >> OPTIC.log 2>> OPTIC.log

  cd ..
done
cd ..

# Launch Popcorn
mkdir popcorn
cd popcorn
for problem in ../../$pName[0-9]
do
  problemN="$(basename $problem)"
  echo $problemN POPCORN
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../popcorn/team4/src/planner/popf/popf3-clp popf3-clp

  timeout ${time} time > POPCORN.log ./popf3-clp ../../../$1 ../../../$problemN >> POPCORN.log 2>> POPCORN.log

  cd ..
done

for problem in ../../$pName[0-9][0-9]
do
  problemN="$(basename $problem)"
  echo $problemN POPCORN
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../popcorn/team4/src/planner/popf/popf3-clp popf3-clp

  timeout ${time} time > POPCORN.log ./popf3-clp ../../../$1 ../../../$problemN >> POPCORN.log 2>> POPCORN.log

  cd ..
done
cd ..


# Launch Temporal FD
mkdir tfd
cd tfd
for problem in ../../$pName[0-9]
do
  problemN="$(basename $problem)"
  echo $problemN Temporal FD
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../tfd/downward/plan plan
  ln -sfn ../../../tfd/downward/plan.py plan.py
  ln -sfn ../../../tfd/downward/build build
  ln -sfn ../../../tfd/downward/search search
  ln -sfn ../../../tfd/downward/preprocess preprocess
  ln -sfn ../../../tfd/downward/translate translate

  timeout ${time} ./plan ../../../$1 ../../../$problemN-time out >> TemporalFD.log 2>> TemporalFD.log

  cd ..
done
for problem in ../../$pName[0-9][0-9]
do
  problemN="$(basename $problem)"
  echo $problemN Temporal FD
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../tfd/downward/plan plan
  ln -sfn ../../../tfd/downward/plan.py plan.py
  ln -sfn ../../../tfd/downward/build build
  ln -sfn ../../../tfd/downward/search search
  ln -sfn ../../../tfd/downward/preprocess preprocess
  ln -sfn ../../../tfd/downward/translate translate

  timeout ${time} ./plan ../../../$1 ../../../$problemN-time out >> TemporalFD.log 2>> TemporalFD.log

  cd ..
done
cd ..

# Launch TFLAP
mkdir tflap
cd tflap
for problem in ../../$pName[0-9]
do
  problemN="$(basename $problem)"
  echo $problemN TFLAP
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../tflap/team2/tflap tflap

  timeout ${time} ./tflap ../../../$1 ../../../$problemN-total out >> TFLAP.log 2>> TFLAP.log

  cd ..
done

for problem in ../../$pName[0-9][0-9]
do
  problemN="$(basename $problem)"
  echo $problemN TFLAP
  mkdir $problemN
  cd $problemN
  ln -sfn ../../../tflap/team2/tflap tflap

  timeout ${time} ./tflap ../../../$1 ../../../$problemN-total out >> TFLAP.log 2>> TFLAP.log

  cd ..
done
cd ..
