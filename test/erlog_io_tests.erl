-module(erlog_io_tests).

-include_lib("eunit/include/eunit.hrl").

read_string_terms_preserves_order_and_variables_test() ->
    ?assertEqual(
       {ok,[first,
            {':-',{second,{'X'}},{first,{'X'}}},
            {third,done}]},
       erlog_io:read_string_terms(
         "first.\nsecond(X) :- first(X).\nthird(done).\n")).

read_string_terms_accepts_empty_source_test() ->
    ?assertEqual({ok,[]}, erlog_io:read_string_terms("\n  % empty\n")).

read_string_terms_accepts_final_dot_without_space_test() ->
    ?assertEqual({ok,[only]}, erlog_io:read_string_terms("only.")).

binary_literal_is_a_term_and_does_not_change_shift_syntax_test() ->
    ?assertEqual(
       {ok,[{payload, <<"a\n">>},
            {is, {'X'}, {'<<', {'X'}, 2}}]},
       erlog_io:read_string_terms(
         "payload(<<\"a\\n\">>).\nX is X << 2.")).

binary_literal_rejects_non_byte_escape_test() ->
    ?assertMatch(
       {error,{1,erlog_parse,invalid_binary_literal}},
       erlog_io:read_string_terms("payload(<<\"\\x100\\\">>).")).

read_string_terms_reports_scanner_line_test() ->
    ?assertMatch(
       {error,{2,erlog_scan,_}},
       erlog_io:read_string_terms("first.\n`.\n")).

read_string_terms_reports_parser_line_test() ->
    ?assertMatch(
       {error,{2,erlog_parse,_}},
       erlog_io:read_string_terms("first.\nfoo(a b).\nlast.\n")).

read_string_terms_reports_actual_ending_line_test() ->
    ?assertEqual(
       {error,{3,erlog_parse,premature_end}},
       erlog_io:read_string_terms("first.\nsecond\n")),
    ?assertEqual(
       {error,{3,erlog_parse,{expected,')'}}},
       erlog_io:read_string_terms("first.\nsecond(a\n")),
    ?assertEqual(
       {error,{3,erlog_parse,no_term}},
       erlog_io:read_string_terms("first.\n:-\n")).

mid_source_expected_error_keeps_token_line_test() ->
    ?assertEqual(
       {error,{2,erlog_parse,{expected,')'}}},
       erlog_io:read_string_terms("first.\nfoo(a b).\n\n\n")).

read_file_uses_actual_ending_line_test() ->
    Path = temp_path(),
    ok = file:write_file(Path, <<"first.\nsecond\n">>),
    try
        ?assertEqual(
           {error,{3,erlog_parse,premature_end}},
           erlog_io:read_file(Path))
    after
        ok = file:delete(Path)
    end.

read_file_accepts_final_dot_without_space_test() ->
    Path = temp_path(),
    ok = file:write_file(Path, <<"only.">>),
    try
        ?assertEqual({ok,[only]}, erlog_io:read_file(Path))
    after
        ok = file:delete(Path)
    end.

temp_path() ->
    filename:join(
      "/tmp",
      "erlog_io_" ++ integer_to_list(erlang:unique_integer([positive])) ++
      ".pl").
