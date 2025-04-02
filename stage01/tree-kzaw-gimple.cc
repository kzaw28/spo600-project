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

// Added headers:
#include "gimple-ssa.h"
#include "cgraph.h"
#include "attribs.h"
#include "pretty-print.h"
#include "tree-inline.h"
#include "intl.h"

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

};

unsigned int
pass_kzaw::execute (function *fun)
{
  basic_block block;
  int block_count = 0, statement_count = 0;

  // Traverse basic blocks in the current function
  FOR_EACH_BB_FN (block, fun)
  {
    block_count++;
    if (dump_file)
    {
      fprintf (dump_file, "===== Basic block count: %d =====\n", block_count);
    }

    // For each basic block, traverse statements
    for (gimple_stmt_iterator gsi = gsi_start_bb (block); !gsi_end_p (gsi); gsi_next (&gsi))
    {
      gimple *g = gsi_stmt (gsi);
      statement_count++;
      if (dump_file)
      {
        fprintf (dump_file, "----- Statement count: %d -----\n", statement_count);
        print_gimple_stmt (dump_file, g, 0, TDF_VOPS|TDF_MEMSYMS);
      }
    }
  }

  // Print summary information
  if (dump_file)
  {
    fprintf (dump_file, "------------------------------------\n");
    fprintf (dump_file, "Total Basic Blocks: %d\n", block_count);
    fprintf (dump_file, "Total Gimple Statements: %d\n", statement_count);
    fprintf (dump_file, "------------------------------------\n\n");
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