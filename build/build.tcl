set project_directory [file dirname [info script]]
set project_name  "flowcutter"

open_project [file join $project_directory $project_name]

launch_runs synth_1
wait_on_run synth_1

launch_runs impl_1
wait_on_run impl_1

open_run impl_1
report_utilization -file [file join $project_directory "utilization.rpt"]
report_timing -max_paths 10 -corner Slow -file [file join $project_directory "timing.rpt"]

close_project
