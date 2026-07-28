/*********************************************************************
 * Authors: Malte Helmert (helmert@informatik.uni-freiburg.de),
 *          Silvia Richter (silvia.richter@nicta.com.au)
 * (C) Copyright 2003-2004 Malte Helmert and Silvia Richter
 * (C) Copyright 2008 NICTA
 *
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

#include "helper_functions.h"
#include "operator.h"
#include "variable.h"

#include <cassert>
#include <iostream>
#include <fstream>
#include <sstream>
using namespace std;

Operator::Operator(istream &in, const vector<Variable *> &variables) {
  check_magic(in, "begin_operator");
  in >> ws;
  getline(in, name);
  int count; // number of prevail conditions
  in >> count;
  for(int i = 0; i < count; i++) {
    int varNo, val;
    in >> varNo >> val;
    prevail.push_back(Prevail(variables[varNo], val));
  }
  in >> count; // number of pre_post conditions
  for(int i = 0; i < count; i++) {
    int eff_conds;
    vector<EffCond> ecs;
    in >> eff_conds;
    for(int j = 0; j < eff_conds; j++) {
      int var, value;
      in >> var >> value;
      ecs.push_back(EffCond(variables[var], value));
    }
    int varNo, val, newVal;
    string funcCost;
    float f_funcCost = 0;
    in >> varNo >> val;
    if (val == -7 || val == -8){
            in >> newVal;
            if(eff_conds)
              pre_block.push_back(PrePost(variables[varNo], ecs, val, newVal, float(-1)));
            else
              pre_block.push_back(PrePost(variables[varNo], val, newVal, float(-1)));
    }
    else if(val != -2 && (val != -3) && (val != -4) && (val != -5) && (val != -6))
    {
        in >> newVal;
        if(eff_conds)
          pre_post.push_back(PrePost(variables[varNo], ecs, val, newVal, float(-1)));
        else
          pre_post.push_back(PrePost(variables[varNo], val, newVal, float(-1)));
    }
    else
    {
    	in >> funcCost >> varNo >> newVal;
    	if (funcCost.find('(') == std::string::npos)
    	{
            istringstream buffer(funcCost);
            buffer >> f_funcCost;
            if(eff_conds)
              pre_post.push_back(PrePost(variables[varNo], ecs, val, newVal, f_funcCost));
            else
              pre_post.push_back(PrePost(variables[varNo], val, newVal, f_funcCost));
    	} else{
            if(eff_conds)
              pre_post.push_back(PrePost(variables[varNo], ecs, val, newVal, float(0),funcCost));
            else
              pre_post.push_back(PrePost(variables[varNo], val, newVal, float(0), funcCost));
    	}
    }

  }
  in >> cost;
  string s_aux = "";
  in >> s_aux;
  if(s_aux == "runtime"){
	  have_runtime_cost = true;
	  in >> runtime_cost;
  } else if (s_aux == "modulefunc"){
	  have_module_cost = true;
	  in >> runtime_cost;
	  cout << name << endl;
  } else {
	  have_runtime_cost = false;
	  have_module_cost = false;
	  in >> s_aux;
  }
  check_magic(in, "end_operator");
}

void Operator::dump() const {
  cout << name << ":" << endl;
  cout << "prevail:";
  for(int i = 0; i < prevail.size(); i++)
    cout << "  " << prevail[i].var->get_name() << " := " << prevail[i].prev;
  cout << endl;
  cout << "pre-post:";
  for(int i = 0; i < pre_post.size(); i++) {
    if(pre_post[i].is_conditional_effect) {
      cout << "  if (";
      for(int j = 0; j < pre_post[i].effect_conds.size(); j++)
	cout << pre_post[i].effect_conds[j].var->get_name() << " := " <<
	  pre_post[i].effect_conds[j].cond;
      cout << ") then";
    }
    cout << " " << pre_post[i].var->get_name() << " : " << 
      pre_post[i].pre <<" -> "<< pre_post[i].post;
  }
  cout << endl;
}

void Operator::strip_unimportant_effects() {
  int new_index = 0;
  for(int i = 0; i < pre_post.size(); i++) {
    if(pre_post[i].var->get_level() != -1)
      pre_post[new_index++] = pre_post[i];
  }
  pre_post.erase(pre_post.begin() + new_index, pre_post.end());
}

bool Operator::is_redundant() const {
  return pre_post.empty();
}

void strip_operators(vector<Operator> &operators) {
  int old_count = operators.size();
  int new_index = 0;
  for(int i = 0; i < operators.size(); i++) {
    operators[i].strip_unimportant_effects();
    if(!operators[i].is_redundant())
      operators[new_index++] = operators[i];
  }
  operators.erase(operators.begin() + new_index, operators.end());
  cout << operators.size() << " of " << old_count << " operators necessary." << endl;
}

void Operator::generate_cpp_input(ofstream &outfile, vector<Variable *> variables) const {
  outfile << "begin_operator" << endl;
  outfile << name << endl;

  outfile << prevail.size() << endl;
  for(int i = 0; i < prevail.size(); i++) {
    assert(prevail[i].var->get_level() != -1);
    if(prevail[i].var->get_level() != -1)
      outfile << prevail[i].var->get_level() << " "<< prevail[i].prev << endl;
  }

  outfile << pre_post.size() << endl;
  for(int i = 0; i < pre_post.size(); i++) { 
    assert(pre_post[i].var->get_level() != -1);
    if(pre_post[i].is_conditional_effect) {
      outfile << pre_post[i].effect_conds.size() << endl;
      for(int j = 0; j < pre_post[i].effect_conds.size(); j++)
	outfile << pre_post[i].effect_conds[j].var->get_level() << " " <<
	  pre_post[i].effect_conds[j].cond << endl;
    } else {
      outfile << "0" << endl;
    }

    if((pre_post[i].pre != -2) && (pre_post[i].pre != -3) && (pre_post[i].pre != -4) && (pre_post[i].pre != -5) && (pre_post[i].pre != -6))
    	outfile << pre_post[i].var->get_level() << " " << pre_post[i].pre << " "
	    	<< pre_post[i].post << endl;
    else
    {
    	if (pre_post[i].have_runtime_cost_effect){

    		string s_effect = pre_post[i].runtime_cost_effect;
    		string s_eff_aux = s_effect;
    		while(s_effect.find("!") != string::npos){
    			string var = "";
    			int i_var;
    			int var_level = 0;
    			s_eff_aux = s_eff_aux.substr(s_eff_aux.find("!") + 1, s_eff_aux.length() - 1);
    			var = s_eff_aux.substr(0, s_eff_aux.find("!"));
    			s_eff_aux = s_eff_aux.substr(s_eff_aux.find("!") + 1, s_eff_aux.length() - 1);
    			stringstream strm(var);
    			strm >> i_var;
    			strm.str(std::string());
    			var_level = variables[i_var]->get_level();
    			std::ostringstream strm_var;
    			strm_var << var_level;

    			string from = "!" + var + "!";
    			string to = ":" + strm_var.str() + ":";
    		    size_t start_pos = 0;
    		    while((start_pos = s_effect.find(from, start_pos)) != std::string::npos) {
    		    	s_effect.replace(start_pos, from.length(), to);
    		        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
    		    }
    		}

    		outfile << pre_post[i].var->get_level() << " " << pre_post[i].pre << " "
    		    	<< pre_post[i].post << " " << s_effect << endl;
    	}
    	else
    		outfile << pre_post[i].var->get_level() << " " << pre_post[i].pre << " "
    		    	<< pre_post[i].post << " " << pre_post[i].f_cost << endl;
    }
  }

  outfile << pre_block.size() << endl;
  for(int i = 0; i < pre_block.size(); i++) {
	  assert(pre_block[i].var->get_level() != -1);
	  if(pre_block[i].is_conditional_effect) {
	    outfile << pre_block[i].effect_conds.size() << endl;
	    for(int j = 0; j < pre_block[i].effect_conds.size(); j++)
	    	outfile << pre_block[i].effect_conds[j].var->get_level() << " " <<
			  pre_post[i].effect_conds[j].cond << endl;
	  } else {
	    outfile << "0" << endl;
	  }

	  outfile << pre_block[i].var->get_level() << " " << pre_block[i].pre << " "
	  	    	<< pre_block[i].post << endl;
  }

  outfile << cost << endl;
  if(have_runtime_cost)
  {
	  outfile << "runtime" << endl;
	  string s_effect = runtime_cost;
	  string s_eff_aux = s_effect;
	  while(s_effect.find("!") != string::npos){
	  		string var = "";
	   		int i_var;
	   		int var_level = 0;
	  		s_eff_aux = s_eff_aux.substr(s_eff_aux.find("!") + 1, s_eff_aux.length() - 1);
	   		var = s_eff_aux.substr(0, s_eff_aux.find("!"));
	   		s_eff_aux = s_eff_aux.substr(s_eff_aux.find("!") + 1, s_eff_aux.length() - 1);
	   		stringstream strm(var);
	   		strm >> i_var;
	   		strm.str(std::string());
	   		var_level = variables[i_var]->get_level();
	   		std::ostringstream strm_var;
	   		strm_var << var_level;
	   		string from = "!" + var + "!";
	   		string to = ":" + strm_var.str() + ":";
      	    size_t start_pos = 0;
  		    while((start_pos = s_effect.find(from, start_pos)) != std::string::npos) {
      		    	s_effect.replace(start_pos, from.length(), to);
      		        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
      		}
      }
	  outfile << s_effect << endl;
  }else if (have_module_cost){
	  outfile << "modulefunc" << endl;
	  outfile << this->runtime_cost << endl;
  }
  else {
	  outfile << "no-run" << endl;
	  outfile << "-" << endl;
  }
  outfile << "end_operator" << endl;
}
