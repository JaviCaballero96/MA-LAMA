/*********************************************************************
 * Authors: Malte Helmert (helmert@informatik.uni-freiburg.de),
 *          Silvia Richter (silvia.richter@nicta.com.au)
 * (C) Copyright 2003-2004 Malte Helmert and Silvia Richter
 * (C) Copyright 2008 NICTA
 * This file is part of LAMA.
 *
 * LAMA is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 3
 * of the license, or (at your option) any later version.
 *
 * LAMA is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 *
 *********************************************************************/

#include <cstdlib>
#include <iostream>
#include <fstream>

#include <string>
#include <vector>
using namespace std;

#include "helper_functions.h"
#include "state.h"
#include "operator.h"
#include "axiom.h"
#include "variable.h"
#include "successor_generator.h"
#include "domain_transition_graph.h"

void check_magic(istream &in, string magic) {
  string word;
  in >> word;
  if(word != magic) {
    cout << "Failed to match magic word '" << magic << "'." << endl;
    cout << "Got '" << word << "'." << endl;
    exit(1);
  }
}

void read_metric(istream &in, string& metric) {

  string aux = "";

  metric = "";
  check_magic(in, "begin_metric");
  in >> aux;
  while(aux != "end")
  {
	  metric = metric + "-" + aux;
	  in >> aux;
  }

  check_magic(in, "end_metric");
}

void read_variables(istream &in, vector<Variable> &internal_variables,
		    vector<Variable *> &variables) {
  check_magic(in, "begin_variables");
  int count;
  in >> count;
  internal_variables.reserve(count);
  // Important so that the iterators stored in variables are valid.
  for(int i = 0; i < count; i++) {
    internal_variables.push_back(Variable(in));
    variables.push_back(&internal_variables.back());
  }
  check_magic(in, "end_variables");
}

void read_shared(istream &in, vector<Variable *> &shared_vars, vector<int> &shared_vars_number,
		const vector<Variable *> &variables) {
  check_magic(in, "begin_shared");
  int count;
  in >> count;
  shared_vars.reserve(count);
  for(int i = 0; i < count; i++) {
	  int var, var2;
	  in >> var >> var2;
	  shared_vars.push_back(variables[var2]);
	  shared_vars_number.push_back(var2);
  }
  check_magic(in, "end_shared");
}

void read_goal(istream &in, const vector<Variable *> &variables,  
	       vector<pair<Variable*, int> > &goals) { 
  check_magic(in, "begin_goal");
  int count;
  in >> count;
  for(int i = 0; i < count; i++) {
    int varNo, val;
    in >> varNo >> val;
    goals.push_back(make_pair(variables[varNo], val));
  }
  check_magic(in, "end_goal");
}

void read_timed_goal(istream &in, const vector<Variable *> &variables,
	       vector<pair<pair<Variable*, int>, vector<pair<pair<Variable*, int>, double> > > > &timed_goals) {
  check_magic(in, "begin_timed_goal");
  int count;
  in >> count;
  for(int i = 0; i < count; i++) {
    int varNo, val;
    in >> varNo >> val;
    //vector<pair<pair<Variable*, int>, double> > empty_vector = vector<pair<pair<Variable*, int>, double> >();
    timed_goals.push_back(make_pair(make_pair(variables[varNo], val), vector<pair<pair<Variable*, int>, double> >()));
    int n_timed_facts = 0;
    in >> n_timed_facts;
    for(int i = 0; i < n_timed_facts; i++){
    	int fvar, fval;
    	double ftime;
    	in >> fvar >> fval >> ftime;
    	timed_goals.back().second.push_back(make_pair(make_pair(variables[fvar], fval), ftime));
    }
    //timed_goals.push_back(make_pair(variables[varNo], val));
  }
  check_magic(in, "end_timed_goal");
}

void read_modules(istream &in, vector<pair<string, vector<pair<string, vector<pair<string, string> > > > > > &modules) {
	  check_magic(in, "begin_modules");
	  int m_count;
	  in >> m_count;
	  for(int i = 0; i < m_count; i++) {
		  string m_name;
		  in >> m_name;
		  modules.push_back(make_pair(m_name, vector<pair<string, vector<pair<string, string> > > >()));
		  modules.back().first = m_name;
		  int f_count;
		  in >> f_count;
		  for(int j = 0; j < f_count; j++) {
			  string f_name;
			  in >> f_name;
			  modules.back().second.push_back(make_pair(f_name, vector<pair<string, string> >()));
			  int arg_count;
			  in >> arg_count;
			  for(int z = 0; z < arg_count; z++) {
				  string arg_name, arg_type;
				  in >> arg_name >> arg_type;
				  modules.back().second.back().second.push_back(make_pair(arg_name, arg_type));
			  }
		  }
	  }
	  check_magic(in, "end_modules");
}

void dump_goal(const vector<pair<Variable*, int> > &goals) {
  cout << "Goal Conditions:" << endl;
  for(int i = 0; i < goals.size(); i++)
    cout << "  " << goals[i].first->get_name() << ": "
	 << goals[i].second << endl;
}

void read_operators(istream &in, const vector<Variable *> &variables, 
		    vector<Operator> &operators) {
  int count;
  in >> count;
  for(int i = 0; i < count; i++)
    operators.push_back(Operator(in, variables));
}
void read_axioms(istream &in, const vector<Variable *> &variables, 
		    vector<Axiom> &axioms) {
  int count;
  in >> count;
  for(int i = 0; i < count; i++)
    axioms.push_back(Axiom(in, variables));
}


void read_preprocessed_problem_description(istream &in,
		               string &metric,
					   vector<Variable> &internal_variables, 
					   vector<Variable *> &variables, 
					   State &initial_state,
					   vector<pair<Variable*, int> > &goals,
					   vector<pair<pair<Variable*, int>, vector<pair<pair<Variable*, int>, double > > > > &timed_goals,
					   vector<Operator> &operators,
					   vector<Axiom> &axioms,
					   vector<Variable *> &shared_vars,
					   vector<int> &shared_vars_number,
					   vector<pair<string, vector<pair<string, vector<pair<string, string> > > > > > &modules) {
  read_metric(in, metric); 
  read_variables(in, internal_variables, variables);
  initial_state = State(in, variables);
  read_shared(in, shared_vars, shared_vars_number, variables);
  read_goal(in, variables, goals);
  read_timed_goal(in, variables, timed_goals);
  read_modules(in, modules);
  read_operators(in, variables, operators);
  read_axioms(in, variables, axioms);
}

void dump_preprocessed_problem_description(const vector<Variable *> &variables, 
					   const State &initial_state,
					   const vector<pair<Variable*, int> > &goals,
					   const vector<Operator> &operators,
					   const vector<Axiom> &axioms) {

  cout << "Variables (" << variables.size() << "):" << endl;
  for(int i = 0; i < variables.size(); i++)
    variables[i]->dump();

  cout << "Initial State:" << endl;
  initial_state.dump();
  dump_goal(goals);

  for(int i = 0; i < operators.size(); i++)
    operators[i].dump();
  for(int i = 0; i < axioms.size(); i++)
    axioms[i].dump();
}

void dump_DTGs(const vector<Variable *> &ordering, 
	       vector<DomainTransitionGraph> &transition_graphs) {
  for(int i = 0; i < transition_graphs.size(); i++) {
    cout << "Domain transition graph for " << ordering[i]->get_name() << ":" << endl;
    transition_graphs[i].dump();
  }
}

std::string ReplaceAll(std::string str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
    }
    return str;
}

void generate_cpp_input(bool solveable_in_poly_time,
			const vector<Variable *> & ordered_vars, 
			const string &metric,
			const State &initial_state,
			const vector<pair<Variable*, int> > &goals,
			const vector<pair<pair<Variable*, int>, vector<pair<pair<Variable*, int>, double> > > > &timed_goals,
			const vector<pair<string, vector<pair<string, vector<pair<string, string> > > > > > modules,
			const vector<Operator> & operators,
			const vector<Axiom> &axioms,
			const SuccessorGenerator &sg,
			const vector<DomainTransitionGraph> transition_graphs,
			const CausalGraph &cg,
			string name,
			vector<Variable *> &shared_vars,
			vector<int> &shared_vars_number,
			vector<Variable *> variables,
			string prefix) {
  ofstream outfile;
  string metric_str;
  string f_name = "output_prepro";
  f_name = f_name + name;
  if(prefix != "")
	  f_name = prefix + "_" + f_name;
  outfile.open(f_name.c_str(),ios::out);
  if(name == "")
	  outfile << "gen" << endl;
  else
	  outfile << name << endl;
  outfile << solveable_in_poly_time << endl; // 1 if true, else 0
  outfile << "begin_metric" << endl;
  metric_str = metric.substr(metric.find("(") + 1, metric.length());
  metric_str = metric_str.substr(0, metric_str.find(")"));
  metric_str = ReplaceAll(metric_str, "-", " ");
  metric_str = metric_str + "end";
  outfile << metric_str << endl;
  outfile << "end_metric" << endl;
  int var_count = ordered_vars.size();
  outfile << "begin_variables" << endl;
  outfile << var_count << endl;
  for(int i = 0; i < var_count; i++) 
    outfile << ordered_vars[i]->get_name()  << " " << 
      ordered_vars[i]->get_range() << " " << ordered_vars[i]->get_layer() << " " << ordered_vars[i]->get_isTotalTime() << endl;
  outfile << "end_variables" << endl;
  outfile << "begin_state" << endl;
  for(int i = 0; i < var_count; i++){
    outfile << initial_state[ordered_vars[i]];// for axioms default value
  	if (initial_state[ordered_vars[i]] == -1)
  	{
  		outfile << " " << initial_state.get_numeric_value(ordered_vars[i]) << endl;
  	}else
  	{
  		outfile << endl;
  	}
  }
  outfile << "end_state" << endl;

  int shared_count = shared_vars.size();
  outfile << "begin_shared" << endl;
  outfile << shared_count << endl;
  vector<string> ordered_shared_values;
  ordered_shared_values.resize(var_count, "-1");
  for(int i = 0; i < shared_vars_number.size(); i++) {
    int var_index = shared_vars[i]->get_level();
    ordered_shared_values[var_index] = shared_vars[i]->get_name();
  }
  for(int i = 0; i < var_count; i++)
    if(ordered_shared_values[i] != "-1")
      outfile << ordered_shared_values[i] << " " <<  i  << " " << endl;
  outfile << "end_shared" << endl;


  vector<int> ordered_goal_values;
  ordered_goal_values.resize(var_count, -1);
  for(int i = 0; i < goals.size(); i++) {
    int var_index = goals[i].first->get_level();
    ordered_goal_values[var_index] = goals[i].second;
  }
  outfile << "begin_goal" << endl;
  outfile << goals.size() << endl;
  for(int i = 0; i < var_count; i++)
    if(ordered_goal_values[i] != -1)
      outfile << i << " " << ordered_goal_values[i] << endl;
  outfile << "end_goal" << endl;

  outfile << "begin_timed_goals" << endl;
  outfile << timed_goals.size() << endl;
  for(int i = 0; i < timed_goals.size(); i++){

	  for(int j = 0; j < var_count; j++){
		  if(ordered_goal_values[j] != -1 &&
				  j == timed_goals[i].first.first->get_level())
			  outfile << j << " " << ordered_goal_values[j] << endl;
	  }

	  outfile << timed_goals[i].second.size() << endl;

	  vector<int> ordered_timed_facts;
	  ordered_timed_facts.resize(var_count, -4);
	  vector<double> ordered_timed_facts_time;
	  ordered_timed_facts_time.resize(var_count, -1);

	  for(int j = 0; j < timed_goals[i].second.size(); j++) {
	      int var_index = timed_goals[i].second[j].first.first->get_level();
	      string name = timed_goals[i].second[j].first.first->get_name();
	      ordered_timed_facts[var_index] = timed_goals[i].second[j].first.second;
	      ordered_timed_facts_time[var_index] = timed_goals[i].second[j].second;

	      outfile << var_index << " " << timed_goals[i].second[j].first.second <<
	     		  " " << timed_goals[i].second[j].second << endl;
	  }

	  /* for(int z = 0; z < var_count; z++) {
		  if(ordered_timed_facts[z] != -4)
			  outfile << z << " " << ordered_timed_facts[z] << " " << ordered_timed_facts_time[z] << endl;
	  }*/
  }
  outfile << "end_timed_goals" << endl;

  outfile << "begin_modules" << endl;
  outfile << modules.size() << endl;
  for(int i = 0; i < modules.size(); i++) {
	  outfile << modules[i].first << endl;
	  outfile << modules[i].second.size() << endl;
	  for(int j = 0; j < modules[i].second.size(); j++) {
		  outfile << modules[i].second[j].first << endl;
		  outfile << modules[i].second[j].second.size() << endl;
		  for(int z = 0; z < modules[i].second[j].second.size(); z++) {
			  outfile << modules[i].second[j].second[z].first << " " << modules[i].second[j].second[z].second << endl;
		  }
	  }
  }
  outfile << "end_modules" << endl;

  outfile << operators.size() << endl;
  for(int i = 0; i < operators.size(); i++)
    operators[i].generate_cpp_input(outfile, variables);

  outfile << axioms.size() << endl;
  for(int i = 0; i < axioms.size(); i++)
    axioms[i].generate_cpp_input(outfile);

  outfile << "begin_SG" << endl;
  sg.generate_cpp_input(outfile);
  outfile << "end_SG" << endl;

  for(int i = 0; i < var_count; i++){
    outfile << "begin_DTG" << endl;
    transition_graphs[i].generate_cpp_input(outfile);
    outfile << "end_DTG" << endl;
  }

  outfile << "begin_CG" << endl;
  cg.generate_cpp_input(outfile, ordered_vars);
  outfile << "end_CG" << endl;

  outfile.close();
}

