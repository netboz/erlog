-include("../src/erlog_int.hrl").

run_properties_test_() ->
    [{atom_to_list(Prop), ?_assert(proper:quickcheck(?MODULE:Prop(),
         [{numtests, 100}, {on_output, fun(S, F) -> io:format(user, S, F) end}]))}
     || {Prop, 0} <- ?MODULE:module_info(exports),
        lists:prefix("prop_", atom_to_list(Prop))].
