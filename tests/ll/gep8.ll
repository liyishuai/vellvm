@gbl = global { i64, [5 x i64], i64} {i64 1, [5 x i64] [i64 2, i64 3, i64 4, i64 5, i64 6], i64 7}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = add i64 0, 0
  %2 = getelementptr { i64, [5 x i64], i64}, { i64, [5 x i64], i64}* @gbl, i32 0, i32 1, i64 %1
  %3 = load i64, i64* %2
  ret i64 %3
}
