set project_directory [file dirname [info script]]
set project_name  "flowcutter"

open_project [file join $project_directory $project_name]

reset_run synth_1

close_project
