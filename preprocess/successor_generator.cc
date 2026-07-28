/*********************************************************************
 * Authors: Malte Helmert (helmert@informatik.uni-freiburg.de),
 *          Silvia Richter (silvia.richter@nicta.com.au)
 * (C) Copyright 2003-2004 Malte Helmert and Silvia Richter
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

#include "operator.h"
#include "successor_generator.h"
#include "variable.h"

#include <functional>
#include <iostream>
#include <fstream>
#include <vector>
#include <cassert>
#include <algorithm>

using namespace std;

/* NOTE on possible optimizations:

   * Sharing "GeneratorEmpty" instances might help quite a bit with
     reducing memory usage and possibly even speed, because there are
     bound to be many instance of those. However, it complicates
     deleting the successor generator, and memory doesn't seem to be
     an issue. Speed appears to be fine now, too. So this is probably
     an unnecessary complication.

   * Using slist instead of list led to a further 10% speedup on the
     largest Logistics instance, logistics-98/prob28.pddl. It would of
     course also reduce memory usage. However, it would make the code
     g++-specific, so it's probably not worth it.

*/

class GeneratorBase {
public:
  virtual ~GeneratorBase() {}
  virtual void dump(string indent) const = 0;
  virtual void generate_cpp_input(ofstream &outfile) const = 0;
};

class GeneratorSwitch : public GeneratorBase {
  Variable *switch_var;
  list<int> immediate_ops_indices;
  vector<GeneratorBase *> generator_for_value;
  GeneratorBase *default_generator;
public:
  ~GeneratorSwitch();
  GeneratorSwitch(Variable *switch_variable,
		  list<int> &operators,
		  const vector<GeneratorBase *> &gen_for_val,
		  GeneratorBase *default_gen);
  virtual void dump(string indent) const;
  virtual void generate_cpp_input(ofstream &outfile) const;
};

class GeneratorLeaf : public GeneratorBase {
  list<int> applicable_ops_indices;
public:
  GeneratorLeaf(list<int> &operators);
  virtual void dump(string indent) const;
  virtual void generate_cpp_input(ofstream &outfile) const;
};

class GeneratorEmpty : public GeneratorBase {
public:
  virtual void dump(string indent) const;
  virtual void generate_cpp_input(ofstream &outfile) const;
};

GeneratorSwitch::GeneratorSwitch(Variable *switch_variable, 
				 list<int> &operators,
				 const vector<GeneratorBase *> &gen_for_val,
				 GeneratorBase *default_gen)
  : switch_var(switch_variable),
    generator_for_value(gen_for_val),
    default_generator(default_gen) {
  immediate_ops_indices.swap(operators);
}

GeneratorSwitch::~GeneratorSwitch() {
  for(int i = 0; i < generator_for_value.size(); i++)
    delete generator_for_value[i];
  delete default_generator;
}

void GeneratorSwitch::dump(string indent) const {
  cout << indent << "switch on " << switch_var->get_name() << endl;
  cout << indent << "immediately:" << endl;
  for(list<int>::const_iterator op_iter = immediate_ops_indices.begin();
      op_iter != immediate_ops_indices.end(); ++op_iter)
    cout << indent << *op_iter << endl;
  for(int i = 0; i < switch_var->get_range(); i++) {
    cout << indent << "case " << i << ":" << endl;
    generator_for_value[i]->dump(indent + "  ");
  }
  cout << indent << "always:" << endl;
  default_generator->dump(indent + "  ");
}

void GeneratorSwitch::generate_cpp_input(ofstream &outfile) const {
  int level = switch_var->get_level();
  assert(level != -1);
  outfile << "switch " << level << endl;
  outfile << "check " << immediate_ops_indices.size() << endl;
  for(list<int>::const_iterator op_iter = immediate_ops_indices.begin();
      op_iter != immediate_ops_indices.end(); ++op_iter)
    outfile << *op_iter << endl;
  for(int i = 0; i < switch_var->get_range(); i++) {
    cout << "case "<<switch_var->get_name()<<" (Level " <<switch_var->get_level() <<
      ") has value " << i << ":" << endl;
    generator_for_value[i]->generate_cpp_input(outfile);
  }
  cout << "always:" << endl;
  default_generator->generate_cpp_input(outfile);
}

GeneratorLeaf::GeneratorLeaf(list<int> &ops) {
  applicable_ops_indices.swap(ops);
}

void GeneratorLeaf::dump(string indent) const {
  for(list<int>::const_iterator op_iter = applicable_ops_indices.begin();
      op_iter != applicable_ops_indices.end(); ++op_iter)
    cout << indent << *op_iter << endl;
}

void GeneratorLeaf::generate_cpp_input(ofstream &outfile) const {
  outfile << "check " << applicable_ops_indices.size() << endl;
  for(list<int>::const_iterator op_iter = applicable_ops_indices.begin();
      op_iter != applicable_ops_indices.end(); ++op_iter)
    outfile << *op_iter << endl;
}

void GeneratorEmpty::dump(string indent) const {
  cout << indent << "<empty>" << endl;
}

void GeneratorEmpty::generate_cpp_input(ofstream &outfile) const {
  outfile << "check 0" << endl;
}

SuccessorGenerator::SuccessorGenerator(const vector<Variable *> &variables,
				       const vector<Operator> &operators) {
  // We need the iterators to conditions to be stable:
  conditions.reserve(operators.size());
  list<int> all_operator_indices;
  // For each operator
  for(int i = 0; i < operators.size(); i++) {
    const Operator *op = &operators[i];
    Condition cond;
    // For each prevail in the operator
    for(int j = 0; j < op->get_prevail().size(); j++) {
      Operator::Prevail prev = op->get_prevail()[j];
      cond.push_back(make_pair(prev.var, prev.prev));
    }
    // For each effect, get also the pre to construct conditions
    for(int j = 0; j < op->get_pre_post().size(); j++) {
      Operator::PrePost pre_post = op->get_pre_post()[j];
      if((pre_post.pre != -1) && ((pre_post.pre != -2) && (pre_post.pre != -3) && (pre_post.pre != -4) && (pre_post.pre != -5) && (pre_post.pre != -6)))
	cond.push_back(make_pair(pre_post.var, pre_post.pre));
    }
    sort(cond.begin(), cond.end());
    // We finally get several vectors: operator indices, conditions and
    // vector of pointers (iterator) to each condition in the
    // conditions vector indexed by operator index
    all_operator_indices.push_back(i);
    conditions.push_back(cond);
    next_condition_by_op.push_back(conditions.back().begin());
  }
  
  varOrder = variables;
  sort(varOrder.begin(), varOrder.end());

  root = construct_recursive(0, all_operator_indices);
}

GeneratorBase *SuccessorGenerator::construct_recursive(int switch_var_no,
						       list<int> &op_indices) {
  if(op_indices.empty())
    return new GeneratorEmpty;

  // Infinite loop
  while(true) {
    // Test if no further switch is necessary (or possible).
    if(switch_var_no == varOrder.size())
      return new GeneratorLeaf(op_indices);

    // Get a pointer to the sorted Variables and its possible values size
    Variable *switch_var = varOrder[switch_var_no];
    int number_of_children = switch_var->get_range();

    // Create a list for each possible value of the variable
    vector<list<int> > ops_for_val_indices(number_of_children);
    list<int> default_ops_indices;
    list<int> applicable_ops_indices;
    
    bool all_ops_are_immediate = true;
    bool var_is_interesting = false;
    
    // While there are operators in op_indices
    while(!op_indices.empty()) {
      // Get the top one
      int op_index = op_indices.front();
      op_indices.pop_front();
      // Assert that the operator is a valid one (>0 and <max)
      assert(op_index >= 0 && op_index < next_condition_by_op.size());
      // Get condition iterator
      Condition::const_iterator &cond_iter = next_condition_by_op[op_index];
      // Assert that the size of the stored conditions is valid
      assert(cond_iter - conditions[op_index].begin() >= 0);
      assert(cond_iter - conditions[op_index].begin() <= conditions[op_index].size());
      // If the extract4ed condition is the last
      if(cond_iter == conditions[op_index].end()) {
    	// Make the var interesting and add the operator to the applicable list
    	  var_is_interesting = true;
    	  applicable_ops_indices.push_back(op_index);
      } else {
    	  // If there exists a condition, then not immediate,
    	  all_ops_are_immediate = false;
    	  // Get variable that presents a condition
    	  Variable *var = cond_iter->first;
    	  // Get index
    	  int val = cond_iter->second;
    	  // If the variable is the switch_var
    	  if(var == switch_var) {
    		  // Var is interesting, get next condition
    		  var_is_interesting = true;
    		  ++cond_iter;
    		  // Store in the operator in the values indexed list
    		  ops_for_val_indices[val].push_back(op_index);
    	  } else {
    		  // If the var is not the switch_var, add the operator to the default list
    		  default_ops_indices.push_back(op_index);
    	  }
      }
    }
    
    // If there aren't any conditions
    if(all_ops_are_immediate) {
    	// Return the generator with the applicable indices
      return new GeneratorLeaf(applicable_ops_indices);
    } else if(var_is_interesting) {
        // Else if the var is interesting --> appears in the conditioins of a operator
      vector<GeneratorBase *> gen_for_val;
      // Iterate over the possible values of the variable
      for(int j = 0; j < number_of_children; j++) {
    	  // Perform the same study for the next switch_var and the operators of each var value
    	  // Add the returned GeneratorBase to gen_for_val, one for each child
    	  gen_for_val.push_back(construct_recursive(switch_var_no + 1,
						  ops_for_val_indices[j]));
      }
      // Perform the same study over the next variable for all default ops (affect a var)
      GeneratorBase *default_sg = construct_recursive(switch_var_no + 1,
						      default_ops_indices);
      return new GeneratorSwitch(switch_var, applicable_ops_indices, gen_for_val, default_sg);
    } else {
      // this switch var can be left out because no operator depends on it
      ++switch_var_no;
      default_ops_indices.swap(op_indices);
    }
  }
}

SuccessorGenerator::SuccessorGenerator() {
  root = 0;
}

SuccessorGenerator::~SuccessorGenerator() {
  delete root;
}

void SuccessorGenerator::dump() const {
  cout << "Successor Generator:" << endl;
  root->dump("  ");
}
void SuccessorGenerator::generate_cpp_input(ofstream &outfile) const {
  root->generate_cpp_input(outfile);
}
