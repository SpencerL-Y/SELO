# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec

import os
from benchexec.tools.sv_benchmarks_util import get_data_model_from_task, ILP32, LP64
import benchexec.tools.template
import benchexec.result as result


class Tool(benchexec.tools.template.BaseTool2):
    """
    This class serves as tool adaptor for ESBMC-SLHV
    """

    def executable(self, tool_locator):
        return tool_locator.find_executable("esbmc-slhv-wrapper.py")

    def working_directory(self, executable):
        executableDir = os.path.dirname(executable)
        return executableDir

    def version(self, executable):
        return self._version_from_tool(executable, "-v")

    def name(self):
        return "ESBMC-SLHV"

    def project_url(self):
        return "todo"

    def cmdline(self, executable, options, task, rlimits):
        data_model_param = get_data_model_from_task(task, {ILP32: "32", LP64: "64"})
        return (
            [executable]
            + ["-p", task.property_file]
            + options
            + [task.single_input_file]
        )

    def determine_result(self, run):
        status = result.RESULT_ERROR

        if run.output.any_line_contains("FALSE_DEREF"):
            status = result.RESULT_FALSE_DEREF
        elif run.output.any_line_contains("FALSE_FREE"):
            status = result.RESULT_FALSE_FREE
        elif run.output.any_line_contains("FALSE_MEMTRACK"):
            status = result.RESULT_FALSE_MEMTRACK
        elif run.output.any_line_contains("FALSE_MEMCLEANUP"):
            status = result.RESULT_FALSE_MEMCLEANUP
        elif run.output.any_line_contains("TRUE_PROP"):
            status = result.RESULT_TRUE_PROP
        elif run.output.any_line_contains("UNKNOWN"):
            status = result.RESULT_UNKNOWN

        return status
