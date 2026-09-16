-module(erlog_observation_tests).
-include_lib("eunit/include/eunit.hrl").
-include("../src/erlog_int.hrl").

%% These tests compare the same interpreter with and without observation.
%% The sink is evaluation-owned ETS, never a process-dictionary mode or a
%% backtrackable binding. It intentionally survives failed derivations.
proof_transparency_test_() ->
    Read = {current_prolog_flag, context, {'C'}},
    Choice = {';', {'=', {'X'}, 1}, {'=', {'X'}, 2}},
    Cases = [
      {plain, true},
      {direct, Read},
      {failed_alternative, {';', {',', Read, fail}, {'=', {'C'}, fallback}}},
      {negation, {'\\+', {',', Read, fail}}},
      {meta_call, {call, Read}},
      {cut, {',', Read, {',', '!', true}}},
      {collector, {findall, {'X'}, {',', Read, {',', Choice, '!'}}, {'L'}}},
      {enumeration, {findall, {'F'}, {current_prolog_flag, {'F'}, {'V'}}, {'L'}}},
      {failed_value, {current_prolog_flag, context, impossible}},
      {absent_flag, {current_prolog_flag, missing, {'V'}}},
      {exception, {',', Read, {call, 42}}},
      {writes, {';', {',', Read, {',', {assertz, staged}, fail}}, true}}
    ],
    [{atom_to_list(Name) ++ ":" ++ atom_to_list(Checkpoints), fun() ->
        St0 = state(),
        St = case Checkpoints of true -> erlog_int:enter_choicepoint_checkpoints(St0); false -> St0 end,
        with_sink(fun(Tab, Sink) ->
            Baseline = result(Goal, St),
            Observed = result(Goal, erlog_int:set_observation_sink(Sink, St)),
            ?assertEqual(normalize(Baseline), normalize(Observed)),
            Events = events(Tab),
            case Name of
                plain -> ?assertEqual([], Events);
                absent_flag -> ?assert(lists:member({flag_lookup, missing}, Events));
                _ -> ?assert(lists:member({flag_value, context, {ctx, tenant, 7}}, Events))
            end
        end)
    end} || Checkpoints <- [false, true], {Name, Goal} <- Cases].

constant_lookup_does_not_read_other_flags_test() ->
    with_sink(fun(Tab, Sink) ->
        {succeed, _} = erlog_int:prove_goal({current_prolog_flag, bounded, false},
          erlog_int:set_observation_sink(Sink, state())),
        ?assertEqual([{flag_lookup, bounded}, {flag_value, bounded, false}], events(Tab))
    end).

redo_observations_survive_failure_test() ->
    with_sink(fun(Tab, Sink) ->
        St = erlog_int:set_observation_sink(Sink, state()),
        {succeed, First} = erlog_int:prove_goal({current_prolog_flag, {'F'}, {'V'}}, St),
        {fail, _} = exhaust(First),
        ?assert(lists:member({flag_value, context, {ctx, tenant, 7}}, events(Tab)))
    end).

cut_pruned_branch_observation_survives_leaving_checkpoints_test() ->
    %% The first alternative reads context and fails. The selected alternative
    %% then cuts away the third; neither pruning nor leaving checkpoint mode
    %% may discard the first alternative's dependency or detach the sink.
    Goal = {',',
            {';', {',', {current_prolog_flag, context, {'C'}}, fail},
                  {';', true, {current_prolog_flag, pruned, {'V'}}}}, '!'},
    with_sink(fun(Tab, Sink) ->
        St = erlog_int:enter_choicepoint_checkpoints(state()),
        {succeed, Baseline} = erlog_int:prove_goal(Goal, St),
        {succeed, Observed} = erlog_int:prove_goal(Goal,
                              erlog_int:set_observation_sink(Sink, St)),
        PlainLeft = erlog_int:leave_choicepoint_checkpoints(Baseline),
        ObservedLeft = erlog_int:leave_choicepoint_checkpoints(Observed),
        ?assertEqual(normalize({succeed, PlainLeft}),
                     normalize({succeed, ObservedLeft})),
        ?assertEqual(0, ObservedLeft#est.checkpoint_depth),
        ?assertMatch({fail, _}, erlog_int:fail(ObservedLeft)),
        Before = events(Tab),
        ?assert(lists:member({flag_value, context, {ctx, tenant, 7}}, Before)),
        ?assertNot(lists:member({flag_lookup, pruned}, Before)),
        Read = {current_prolog_flag, bounded, false},
        ?assertEqual(normalize(result(Read, PlainLeft)),
                     normalize(result(Read, ObservedLeft))),
        ?assertEqual(Before ++ [{flag_lookup, bounded}, {flag_value, bounded, false}],
                     events(Tab))
    end).

native_entry_is_explicitly_unclassified_test() ->
    with_sink(fun(Tab, Sink) ->
        {succeed, _} = erlog_int:prove_goal({is, {'N'}, {'+', 1, 2}},
          erlog_int:set_observation_sink(Sink, state())),
        ?assert(lists:member({native, erlog_bips, prove_goal, {is, 2}}, events(Tab)))
    end).

internal_unknown_flag_is_observed_test() ->
    with_sink(fun(Tab, Sink) ->
        St = erlog_int:set_observation_sink(Sink, state()),
        {erlog_error, _, _} = result(unknown_predicate, St),
        ?assert(lists:member({flag_value, unknown, error}, events(Tab)))
    end).

sink_failure_is_not_silent_incomplete_success_test() ->
    St = erlog_int:set_observation_sink(fun(_) -> error(observation_failed) end, state()),
    ?assertError(observation_failed, erlog_int:prove_goal({current_prolog_flag, bounded, false}, St)).

state() ->
    {ok, St} = erlog_int:new(erlog_db_dict, null),
    Db = lists:foldl(fun(Mod, Acc) -> Mod:load(Acc) end,
                    St#est.db, [erlog_bips, erlog_lib_dcg, erlog_lib_lists]),
    St#est{db=Db,fs=[{context, {ctx, tenant, 7}, none} | St#est.fs]}.

with_sink(Fun) ->
    Tab = ets:new(observations, [ordered_set]),
    Sink = fun(Event) -> true = ets:insert(Tab, {erlang:unique_integer([monotonic]), Event}), ok end,
    try Fun(Tab, Sink) after ets:delete(Tab) end.

events(Tab) -> [Event || {_, Event} <- ets:tab2list(Tab)].
result(Goal, St) -> try erlog_int:prove_goal(Goal, St) catch throw:E -> E end.
normalize({Tag, St = #est{}}) -> {Tag, St#est{observation_sink=none}};
normalize({Tag, Why, St = #est{}}) -> {Tag, Why, St#est{observation_sink=none}}.
exhaust(St) -> case erlog_int:fail(St) of {succeed, Next} -> exhaust(Next); Other -> Other end.
