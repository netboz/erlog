-module(erlog_choicepoint_owned_tests).

-include_lib("eunit/include/eunit.hrl").
-include("../src/erlog_int.hrl").

-export([cp_counter_2/3]).

owned_data_survives_relation_clause_retry_test() ->
    St0 = state(),
    Db1 = erlog_int:add_compiled_proc(
            {cp_counter, 1}, ?MODULE, cp_counter_2, St0#est.db),
    Clauses = [
        {':-', {owned_choice, first}, {cp_counter, 0}},
        {':-', {owned_choice, second}, {cp_counter, 1}},
        {':-', {owned_choice, third}, {cp_counter, 2}}
    ],
    St1 = lists:foldl(fun assert_clause/2, St0#est{db=Db1}, Clauses),
    {succeed, First} = erlog_int:prove_goal({owned_choice, {'X'}}, St1),
    ?assertEqual(first, erlog_int:dderef({'X'}, First#est.bs)),
    {succeed, Second} = erlog_int:fail(First),
    ?assertEqual(second, erlog_int:dderef({'X'}, Second#est.bs)).

%% Exhausting every alternative pops the governing choice point, so a later
%% activation of the same relation must start from an empty map.  Retained
%% state would make the second activation read 2 and refuse.
owned_data_is_gone_after_relation_exhaustion_test() ->
    Clauses = [
        {':-', {owned_exhaust, 1}, {',', {cp_counter, 0}, fail}},
        {':-', {owned_exhaust, 1}, {',', {cp_counter, 1}, fail}},
        {':-', {owned_exhaust, 2}, {cp_counter, 0}},
        {':-', {owned_exhaust, 3}, fail}
    ],
    ?assertMatch(
       {succeed, _},
       prove_clauses(
         Clauses, {';', {owned_exhaust, 1}, {owned_exhaust, 2}})).

%% A cut discards the governing choice point with its owned map, so the next
%% activation is equally fresh.
owned_data_is_gone_after_cut_test() ->
    Clauses = [
        {':-', {owned_cut, 1},
         {',', {cp_counter, 0}, {',', '!', fail}}},
        {':-', {owned_cut, 2}, {cp_counter, 0}},
        {':-', {owned_cut, 3}, fail}
    ],
    ?assertMatch(
       {succeed, _},
       prove_clauses(Clauses, {';', {owned_cut, 1}, {owned_cut, 2}})).

%% Two live activations of the same relation own separate maps.  State held
%% outside the interpreter could not tell them apart, so the inner counter
%% would read the outer's 1 and refuse.
owned_data_is_per_activation_test() ->
    Clauses = [
        {':-', owned_nested_outer,
         {',', {cp_counter, 0}, owned_nested_inner}},
        {':-', owned_nested_outer, fail},
        {':-', owned_nested_inner, {cp_counter, 0}},
        {':-', owned_nested_inner, fail}
    ],
    ?assertMatch({succeed, _}, prove_clauses(Clauses, owned_nested_outer)).

prove_clauses(Clauses, Goal) ->
    St0 = state(),
    Db1 = erlog_int:add_compiled_proc(
            {cp_counter, 1}, ?MODULE, cp_counter_2, St0#est.db),
    St1 = lists:foldl(fun assert_clause/2, St0#est{db=Db1}, Clauses),
    erlog_int:prove_goal(Goal, St1).

cp_counter_2(Goal, Next, #est{bs=Bs,cps=Cps}=St) ->
    {cp_counter, Expected} = erlog_int:dderef(Goal, Bs),
    case update_counter(Expected, Cps) of
        {ok, Cps1} -> erlog_int:prove_body(Next, St#est{cps=Cps1});
        error -> erlog_int:fail(St)
    end.

update_counter(Expected, [Cp=#cp{type=goal_clauses,owned=Owned}|Rest]) ->
    case maps:get(?MODULE, Owned, 0) of
        Expected ->
            {ok, [Cp#cp{owned=Owned#{?MODULE => Expected + 1}}|Rest]};
        _Other ->
            error
    end;
update_counter(Expected, [Cp|Rest]) ->
    case update_counter(Expected, Rest) of
        {ok, Rest1} -> {ok, [Cp|Rest1]};
        error -> error
    end;
update_counter(_Expected, []) ->
    error.

assert_clause(Clause, St) ->
    {succeed, Next} = erlog_int:prove_goal({assertz, Clause}, St),
    Next.

state() ->
    {ok, Erl} = erlog:new(erlog_db_dict, null),
    element(3, Erl).
