"""One ordered 23-stage bounded diagnostic, with an explicit execution trace."""


def mandatory(read_json):
    trace, results = [], {}
    first = indexed(read_json)
    trace.extend(first["order"])
    results["indexed"] = first["controls"]
    calibrate = calibration(read_json)
    trace.extend(calibrate["order"])
    results["calibration"] = calibrate
    results["uniform6"] = uniform6(read_json)
    trace.append("I176_k6")
    results["adjacent"], S = adjacent(read_json)
    trace.append("I177_child_absorption")
    results["presentation"] = presentation(read_json,S)
    trace.append("I178_relations_completion")
    results["lock"] = lock(read_json,S)
    trace.append("I179_lock")
    results["parent_helper"] = helper_identities(read_json,S)
    trace.append("parent_helper")
    results["helper_graph"] = helper_graph(read_json,S)
    trace.append("I180_helpergraph")
    results["patch"] = patch_control(read_json)
    trace.append("I181_patch_reattachment")
    results["reduction"] = reduction(read_json,S)
    trace.append("I182_reduction_finite")
    assert trace == ALL_STAGES and len(trace)==23
    return {"status":"PASS_23_BOUNDED_STAGES","order":trace,"results":results,
            "boundary_order":S["boundary_order"],"E183":"UNRESOLVED"}
