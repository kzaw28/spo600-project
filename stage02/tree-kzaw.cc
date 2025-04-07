#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "tree-pretty-print.h"
#include "gimple-iterator.h"
#include "gimple-walk.h"
#include "internal-fn.h"
#include "gimple-pretty-print.h"

// Additional headers needed for clone analysis
#include "gimple-ssa.h"
#include "cgraph.h"
#include "attribs.h"
#include "pretty-print.h"
#include "tree-inline.h"
#include "intl.h"
#include <map>
#include <string>
#include <vector>

namespace {

const pass_data pass_data_kzaw =
{
  GIMPLE_PASS, /* type */
  "kzaw", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_TREE_NRV, /* tv_id */
  PROP_cfg , /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_kzaw : public gimple_opt_pass
{
public:
  pass_kzaw (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_kzaw, ctxt)
  {}

  bool gate (function *) final override {
    return 1;
  }

  unsigned int execute (function *) final override;

private:
  // Data structure to store function information
  struct function_info {
    tree decl;                 // Function declaration
    function *fun;             // Function pointer
    std::string base_name;     // Base function name (without variant)
    std::string variant;       // Variant part of the name
    std::vector<gimple *> stmts; // Statements in the function
  };

  std::map<std::string, std::vector<function_info>> clone_groups;

  // Helper methods
  bool is_clone_function(tree decl, std::string &base_name, std::string &variant);
  void collect_function_statements(function *fun, std::vector<gimple *> &stmts);
  bool compare_functions(const std::vector<gimple *> &func1_stmts, 
                         const std::vector<gimple *> &func2_stmts);
  void print_prune_decision(const std::string &base_name, bool should_prune);
};

// Check if a function is a clone
bool
pass_kzaw::is_clone_function(tree decl, std::string &base_name, std::string &variant)
{
  // Get the function name
  const char *full_name = IDENTIFIER_POINTER(DECL_NAME(decl));
  std::string func_name(full_name);

  // Look for the '.variant' pattern in the function name
  size_t dot_pos = func_name.find('.');
  if (dot_pos != std::string::npos) {
    base_name = func_name.substr(0, dot_pos);
    variant = func_name.substr(dot_pos);

    // Skip resolver functions
    if (variant == ".resolver") {
      return false;
    }

    if (dump_file) {
      fprintf(dump_file, "Found potential clone: %s (base: %s, variant: %s)\n", 
              full_name, base_name.c_str(), variant.c_str());
    }
    return true;
  }

  return false;
}

// Collect all statements from a function
void
pass_kzaw::collect_function_statements(function *fun, std::vector<gimple *> &stmts)
{
  basic_block bb;

  // Clear the vector in case it's being reused
  stmts.clear();

  // Collect all statements in the function
  FOR_EACH_BB_FN(bb, fun) {
    for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi); gsi_next(&gsi)) {
      gimple *stmt = gsi_stmt(gsi);
      stmts.push_back(stmt);
    }
  }

  if (dump_file) {
    fprintf(dump_file, "Collected %zu statements from function %s\n", 
            stmts.size(), function_name(fun));
  }
}

// Compare two functions for substantial similarity
bool
pass_kzaw::compare_functions(const std::vector<gimple *> &func1_stmts, 
                             const std::vector<gimple *> &func2_stmts)
{
  // First check: different statement count means different functions
  if (func1_stmts.size() != func2_stmts.size()) {
    if (dump_file) {
      fprintf(dump_file, "Functions have different statement counts: %zu vs %zu\n", 
              func1_stmts.size(), func2_stmts.size());
    }
    return false;
  }

  // Maps to track equivalent SSA names between the two functions
  std::map<tree, tree> ssa_map;
  
  // Iterate through statements and compare them
  for (size_t i = 0; i < func1_stmts.size(); i++) {
    gimple *stmt1 = func1_stmts[i];
    gimple *stmt2 = func2_stmts[i];
    
    // Check if statement codes are different
    if (gimple_code(stmt1) != gimple_code(stmt2)) {
      if (dump_file) {
        fprintf(dump_file, "Statement %zu: Different gimple codes\n", i);
        print_gimple_stmt(dump_file, stmt1, 0, TDF_SLIM);
        print_gimple_stmt(dump_file, stmt2, 0, TDF_SLIM);
      }
      return false;
    }
    
    // Compare based on statement type
    switch (gimple_code(stmt1)) {
    case GIMPLE_ASSIGN:
      {
        // Check operation code
        if (gimple_assign_rhs_code(stmt1) != gimple_assign_rhs_code(stmt2)) {
          if (dump_file) {
            fprintf(dump_file, "Assignment operation mismatch at statement %zu\n", i);
          }
          return false;
        }
        
        // Check operand count
        unsigned op_count1 = gimple_num_ops(stmt1);
        unsigned op_count2 = gimple_num_ops(stmt2);
        if (op_count1 != op_count2) {
          if (dump_file) {
            fprintf(dump_file, "Different number of operands at statement %zu\n", i);
          }
          return false;
        }
        
        // For constants and literals, values must match exactly
        for (unsigned j = 1; j < op_count1; j++) {
          tree op1 = gimple_op(stmt1, j);
          tree op2 = gimple_op(stmt2, j);
          
          if (TREE_CODE(op1) != TREE_CODE(op2)) {
            if (dump_file) {
              fprintf(dump_file, "Different operand types at statement %zu\n", i);
            }
            return false;
          }
          
          // For constants, compare values
          if (CONSTANT_CLASS_P(op1) && CONSTANT_CLASS_P(op2)) {
            if (!vrp_operand_equal_p(op1, op2)) {
              if (dump_file) {
                fprintf(dump_file, "Different constant values at statement %zu\n", i);
              }
              return false;
            }
          }
        }
      }
      break;
      
    case GIMPLE_CALL:
      {
        // Check if calling the same function
        tree func1 = gimple_call_fn(as_a<gcall *>(stmt1));
        tree func2 = gimple_call_fn(as_a<gcall *>(stmt2));
        
        if (TREE_CODE(func1) != TREE_CODE(func2)) {
          if (dump_file) {
            fprintf(dump_file, "Different function call types at statement %zu\n", i);
          }
          return false;
        }
        
        // If it's a direct function call, compare the function declarations
        if (TREE_CODE(func1) == ADDR_EXPR) {
          tree fn_decl1 = TREE_OPERAND(func1, 0);
          tree fn_decl2 = TREE_OPERAND(func2, 0);
          
          if (DECL_NAME(fn_decl1) != DECL_NAME(fn_decl2)) {
            if (dump_file) {
              fprintf(dump_file, "Calling different functions at statement %zu\n", i);
            }
            return false;
          }
        }
        
        // Check argument count
        unsigned arg_count1 = gimple_call_num_args(as_a<gcall *>(stmt1));
        unsigned arg_count2 = gimple_call_num_args(as_a<gcall *>(stmt2));
        if (arg_count1 != arg_count2) {
          if (dump_file) {
            fprintf(dump_file, "Different number of arguments in call at statement %zu\n", i);
          }
          return false;
        }
      }
      break;
      
    case GIMPLE_COND:
      {
        // Check condition code
        enum tree_code code1 = gimple_cond_code(as_a<gcond *>(stmt1));
        enum tree_code code2 = gimple_cond_code(as_a<gcond *>(stmt2));
        if (code1 != code2) {
          if (dump_file) {
            fprintf(dump_file, "Different conditional codes at statement %zu\n", i);
          }
          return false;
        }
      }
      break;
      
    case GIMPLE_RETURN:
      {
        // Check if one returns a value and the other doesn't
        tree ret_val1 = gimple_return_retval(as_a<greturn *>(stmt1));
        tree ret_val2 = gimple_return_retval(as_a<greturn *>(stmt2));
        
        if ((ret_val1 == NULL_TREE) != (ret_val2 == NULL_TREE)) {
          if (dump_file) {
            fprintf(dump_file, "One function returns a value, the other doesn't at statement %zu\n", i);
          }
          return false;
        }
      }
      break;
      
    default:
      // For other statement types, we consider them the same if the code matches
      break;
    }
  }
  
  // If we've made it this far, the functions are considered substantially the same
  if (dump_file) {
    fprintf(dump_file, "Functions are substantially the same\n");
  }
  return true;
}

// Print the pruning decision
void
pass_kzaw::print_prune_decision(const std::string &base_name, bool should_prune)
{
  if (dump_file) {
    if (should_prune) {
      fprintf(dump_file, "PRUNE: %s\n", base_name.c_str());
    } else {
      fprintf(dump_file, "NOPRUNE: %s\n", base_name.c_str());
    }
  }
}

// Main execution function for the pass
unsigned int
pass_kzaw::execute(function *fun)
{
  // Get the function declaration
  tree fndecl = current_function_decl;
  
  // Skip external functions or those with no body
  if (!fndecl || DECL_EXTERNAL(fndecl) || !DECL_STRUCT_FUNCTION(fndecl)) {
    return 0;
  }
  
  // Check if this is a clone function
  std::string base_name, variant;
  bool is_clone = is_clone_function(fndecl, base_name, variant);
  
  if (is_clone) {
    // Collect statements in this function
    function_info info;
    info.decl = fndecl;
    info.fun = fun;
    info.base_name = base_name;
    info.variant = variant;
    collect_function_statements(fun, info.stmts);
    
    // Add to the appropriate clone group
    clone_groups[base_name].push_back(info);
    
    // Check if we've seen enough clones of this function to make a decision
    if (clone_groups[base_name].size() >= 2) {
      if (dump_file) {
        fprintf(dump_file, "Analyzing clones of function: %s\n", base_name.c_str());
      }
      
      // Compare the first two variants
      const function_info &info1 = clone_groups[base_name][0];
      const function_info &info2 = clone_groups[base_name][1];
      
      bool are_same = compare_functions(info1.stmts, info2.stmts);
      
      // Print the pruning decision
      print_prune_decision(base_name, are_same);
      
      // Clear the clone group after making the decision
      // This ensures we only emit one decision per base function
      clone_groups.erase(base_name);
    }
  }
  
  return 0;
}

} // anonymous namespace

// Factory function that creates an instance of the pass
gimple_opt_pass *
make_pass_kzaw (gcc::context *ctxt)
{
  return new pass_kzaw (ctxt);
}