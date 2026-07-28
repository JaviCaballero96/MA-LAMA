import os
import fnmatch


def take_time(elem):
    return elem[2][3]


def const_fase_create_plan():
    local_path = os.getcwd() + "/step_0/"
    count = -1
    agent_number = 0
    filename_per_agent = []
    file_per_agent = []
    total_time_metric = False

    # Check file from step0
    if not os.path.exists(local_path):
        return []

    # Count agents number and get the last solution found for each
    while count != 0:
        match = 'output_preproagent' + str(agent_number) + '.p*'
        count = len(fnmatch.filter(os.listdir(local_path), match))
        if count != 0:
            files_per_agent = fnmatch.filter(os.listdir(local_path), match)
            files_per_agent.sort(reverse=True)
            filename_per_agent.append(files_per_agent[0])
            file_per_agent.append(open(local_path + filename_per_agent[agent_number], "r"))
            print("Agent " + str(agent_number) + " --> " + filename_per_agent[agent_number])
        agent_number = agent_number + 1
        # print(match + " -> Agent " + str(agent_number) + ": " + str(count))

    agent_number = agent_number - 1
    print(str(agent_number) + " agents detected in the step_0")

    # read all agent plans
    read_plans = []
    for file in file_per_agent:
        read_plan = []
        time = 0
        line_number = 0
        append_bool = True
        for line in file:
            if "Cost:" not in line and "Expanded nodes" not in line and "Search time" not in line:
                duration = line.split("(")[0]
                action_init_time = duration.split(" ")[1].strip()
                duration = duration.split(" ")[0].strip()

                line = line.split("(")[1:][0]
                name = line.split(")")[0]
                cost = line.split(")")[1].strip()
                if "_end" not in name:
                    if duration == "0":
                        duration = "0.001"
                read_plan.append([duration, name, cost, float(action_init_time)])

                if "_end" not in name:
                    time = float(action_init_time)

            else:
                print(line)
                if "Total-time Cost" in line:
                    total_time_metric = True
                if line_number == 0:
                    append_bool = False
                    agent_number = agent_number - 1
                    break

            line_number = line_number + 1

        if append_bool:
            read_plans.append(read_plan)

    for a_file in file_per_agent:
        a_file.close()

    # Create final plan
    local_plan = []
    all_plans_finished = False
    agent_plan_finished = [False] * agent_number
    agent_counter = [0] * agent_number
    tick = 0

    # we will only finish this when all plans have finished
    iterations = 0
    current_constraints = {}
    while not all_plans_finished:
        agent_checked = 0
        candidates = [None] * agent_number

        # get counter actions that have a start time minor than the general tick
        for agent_plan in read_plans:
            # Check if counter action can be added
            if not agent_plan_finished[agent_checked]:
                action = agent_plan[agent_counter[agent_checked]]

                # an action can be added if the tick time is greater and there are no other agent actions with less tick
                if tick >= action[3]:
                    candidates[agent_checked] = [agent_counter[agent_checked], agent_checked, action]

            agent_checked = agent_checked + 1

        added_action = False
        while not added_action:

            all_none = True
            for act in candidates:
                if act is not None:
                    all_none = False
            if all_none:
                tick = tick + 0.001
                break

            # get the candidate with the minimum start time
            action_to_include = None
            for action in candidates:
                if action is not None:
                    if action_to_include is None:
                        action_to_include = action
                    else:
                        if action_to_include[2][3] > action[2][3]:
                            action_to_include = action

            if action_to_include is not None:
                valid_candidate = True

                if valid_candidate:
                    added_action = True
                    # Keep the action's own precise time. The tick is only
                    # a cursor for finding the next action chronologically,
                    # not a value to round the recorded time to.
                    local_plan.append(action_to_include)
                    agent_counter[action_to_include[1]] = action_to_include[0] + 1

                    if agent_counter[action_to_include[1]] >= len(read_plans[action_to_include[1]]):
                        agent_plan_finished[action_to_include[1]] = True
                        all_plans_finished = True
                        for boolean_finished in agent_plan_finished:
                            if not boolean_finished:
                                all_plans_finished = False
                                break
                else:
                    candidates.remove(action_to_include)

            else:
                tick = tick + 0.001

        iterations = iterations + 1

    return local_plan, total_time_metric, agent_number


def coop_fase_create_plan(curr_time_followupn):
    # Create final plan
    local_plan = []
    local_path = os.getcwd() + "/"

    match = 'step_*'
    step_number = len(fnmatch.filter(os.listdir(local_path), match))

    match = '*general*'
    if len(fnmatch.filter(os.listdir(local_path + "step_" + str(step_number - 1) + "/"), match)) > 0:
        step_number = step_number - 1

    init_const = 0
    if os.path.exists(local_path + "step_0"):
        step_number = step_number - 1
        init_const = 1

    print(str(step_number) + " coop detected in root directory")

    for dir_num in range(init_const, step_number + 1):
        print("Analyzing dir step_" + str(dir_num))
        coop_dir_path = local_path + "step_" + str(dir_num) + "/"

        agent_filenames_ordered = []
        file_per_agent_ordered = []
        match_found = True
        match_index = 0
        while match_found:
            match = str(match_index) + '_output*.sas'
            match_found = len(fnmatch.filter(os.listdir(coop_dir_path), match)) == 1
            if match_found:
                agent_filenames_ordered.append(fnmatch.filter(os.listdir(coop_dir_path), match)[0])
                # file_per_agent_ordered.append(open(coop_dir_path + agent_filenames_ordered[match_index], "r"))

                match_index = match_index + 1
        file_per_agent_ordered = []
        f_index = 0
        for agent_filename in agent_filenames_ordered:
            coop_dir_file = coop_dir_path + str(f_index) + "_output_preproagent" + \
                            ((agent_filename.split("_")[-1]).split(".sas")[0]).split("agent")[-1] + ".1"
            file_per_agent_ordered.append(open(coop_dir_file, "r"))
            f_index = f_index + 1
        for file in agent_filenames_ordered:
            print("Current file: " + file + " agent number " + file.split("_")[0] + " is " +
                  (file.split("_")[-1]).split(".sas")[0] + " " +
                  ((file.split("_")[-1]).split(".sas")[0]).split("agent")[-1])

        # Read the file and directly apply it to the plan since it is already ordered
        # curr time is given in the function arguments
        f_index = 0
        for a_file in file_per_agent_ordered:
            local_file_plan = []
            line_number = 0
            print("Time init for coop phase " + str(agent_filenames_ordered[f_index]) +
                  " --> " + str(float(curr_time_followup)))
            for line in a_file:
                if "Cost:" not in line and "Expanded nodes" not in line and "Search time" not in line:
                    duration = line.split("(")[0]
                    action_init_time = duration.split(" ")[1].strip()
                    duration = duration.split(" ")[0].strip()

                    line = line.split("(")[1:][0]
                    name = line.split(")")[0]
                    cost = line.split(")")[1].strip()
                    if "_end" not in name:
                        if duration == "0":
                            duration = "0.001"
                    local_file_plan.append([duration, name, cost, float(curr_time_followup)])

                    if "_end" not in name:
                        curr_time_followup = float(duration) + float(curr_time_followup)

                else:
                    if "Total-time Cost" in line:
                        TOTAL_TIME_METRIC = True
                    if line_number == 0:
                        break

                line_number = line_number + 1

            act_index = 0
            for lf_action in local_file_plan:
                local_plan.append(
                    [act_index,
                     int(((agent_filenames_ordered[f_index].split("_")[-1]).split(".sas")[0]).split("agent")[-1]),
                     lf_action])
                act_index = act_index + 1

            # curr_time_followup = local_plan[-1][2][3]
            f_index = f_index + 1

    return local_plan


def general_fase_create_plan(curr_time_followup):
    # Create final plan
    local_plan = []
    local_path = os.getcwd() + "/"

    match = 'step_*'
    step_number = len(fnmatch.filter(os.listdir(local_path), match))

    match = 'output_preprogeneral.1'
    if len(fnmatch.filter(os.listdir(local_path + "step_" + str(step_number - 1) + "/"), match)) <= 0:
        return []

    print("General goals plan found!")

    g_file = open(local_path + "step_" + str(step_number - 1) + "/output_preprogeneral.1", "r")
    local_file_plan = []
    line_number = 0
    for line in g_file:
        if "Cost:" not in line and "Expanded nodes" not in line and "Search time" not in line:
            duration = line.split("(")[0]
            action_init_time = duration.split(" ")[1].strip()
            duration = duration.split(" ")[0].strip()

            line = line.split("(")[1:][0]
            name = line.split(")")[0]
            cost = line.split(")")[1].strip()
            if "_end" not in name:
                if duration == "0":
                    duration = "0.001"
            local_file_plan.append([duration, name, cost, float(curr_time_followup)])

            if "_end" not in name:
                curr_time_followup = float(duration) + float(curr_time_followup)

        else:
            if line_number == 0:
                break

        line_number = line_number + 1

    act_index = 0
    for lf_action in local_file_plan:
        local_plan.append([act_index, -1, lf_action])
        act_index = act_index + 1

    return local_plan


if __name__ == '__main__':

    curr_time = 0
    plan_step_const, total_time_metric, n_agents = const_fase_create_plan()
    if plan_step_const:
        curr_time = float(plan_step_const[-1][2][3]) + float(plan_step_const[-1][2][0])
        print("End coordination phase time: " + str(curr_time))

    plan_step_coop = coop_fase_create_plan(curr_time)
    if plan_step_coop:
        curr_time = float(plan_step_coop[-1][2][3]) + float(plan_step_coop[-1][2][0])
        print("End cooperation phase time: " + str(curr_time))

    plan_step_general = general_fase_create_plan(curr_time)
    if plan_step_general:
        curr_time = float(plan_step_coop[-1][2][3]) + float(plan_step_coop[-1][2][0])
        print("End general phase time: " + str(curr_time))
    # print only start actions in final plan

    final_plan = plan_step_const + plan_step_coop + plan_step_general
    dir_path = os.getcwd() + "/"
    plan_cost = 0
    last_action_init = 0
    last_action_dur = 0
    # Calculate plan duration and read min_valid_time to calculate max application window for all actions
    plan_makespan = [0] * n_agents
    for action in final_plan:
        if "_start" in action[2][1]:
            plan_makespan[action[1]] = plan_makespan[action[1]] + float(action[2][0])
    min_valid_time_windows = []
    inf = False
    try:
        f = open("unify_info.txt", "r")
    except:
        inf = True
        print("No negative time windows are present")
    if not inf:
        lines = [line.rstrip() for line in f]
        assert(lines[0] == "Unify Data")
        for window in lines[1:]:
            min_valid_time_windows.append(float(window))
        print(min_valid_time_windows)

    final_plan_file = open(dir_path + "final_plan.txt", 'w')
    GMV_final_plan_file = open(dir_path + "final_plan_time.txt", 'w')
    final_plan.sort(key=take_time)
    plan_duration_sum = [0] * n_agents

    for action in final_plan:
        print(action)
        if "_start" in action[2][1]:
            action_name = action[2][1].split("_start")[0] + action[2][1].split("_start")[1]
            action_init = action[2][3]
            action_duration = float(action[2][0])
            plan_cost = plan_cost + float(action[2][2])
            final_plan_file.write(
                "{:.3f}".format(action_init) + " " + "({:.3f})".format(action_duration) + " " + str(action_name) + "\n")

            # Calculate the end time window

            if min_valid_time_windows:
                found_i = -1
                time_window = min_valid_time_windows[-1]
                index = 0
                for elem in min_valid_time_windows:
                    if action_init <= elem:
                        time_window = elem
                        found_i = index
                        break
                    index = index + 1

                # Calculate real applicable makespan
                if time_window == min_valid_time_windows[-1]:
                    real_plan_makespan = plan_makespan[action[1]]
                else:
                    real_plan_makespan = 0
                    for act in final_plan:
                        if "_start" in act[2][1]:
                            if act[1] == action[1] and float(act[2][3]) + 3 < min_valid_time_windows[found_i]:
                                real_plan_makespan = real_plan_makespan + float(act[2][0])

                time_window_value = time_window - (real_plan_makespan - plan_duration_sum[action[1]])

                # GMV_final_plan_file.write(
                #     str(time_window) + " - (" + str(real_plan_makespan) + " - " + str(plan_duration_sum[action[1]]) + ")\n")

                plan_duration_sum[action[1]] = plan_duration_sum[action[1]] + float(action[2][0])

                GMV_final_plan_file.write(
                    str(action_name) + " [" + "{:.3f}".format(action_init) + ", " + "{:.3f}".format(time_window_value) + ", " +
                    "{:.3f}".format(action_duration) + "]" + "\n")
            else:
                GMV_final_plan_file.write(
                    str(action_name) + " [" + "{:.3f}".format(action_init) + ", " + "inf" + ", " +
                    "{:.3f}".format(action_duration) + "]" + "\n")
            last_action_init = action_init
            last_action_dur = action_duration
        elif "_end" in action[2][1]:
            plan_cost = plan_cost + float(action[2][2])
        else:
            action_name = action[2][1]
            action_init = action[2][3]
            action_duration = float(action[2][0])
            plan_cost = plan_cost + float(action[2][2])
            final_plan_file.write(
                "{:.3f}".format(action_init) + " " + "({:.3f})".format(action_duration) + " " + str(action_name) + "\n")
            last_action_init = action_init
            last_action_dur = action_duration

    if total_time_metric:
        final_plan_file.write("Cost: " + "{:.3f}".format(action_init + last_action_dur) + "\n")
    else:
        final_plan_file.write("Cost: " + str(plan_cost) + "\n")
    final_plan_file.write("Makespan: " + str(last_action_init + last_action_dur) + "\n")
    final_plan_file.close()
    GMV_final_plan_file.close()
    print("end")
