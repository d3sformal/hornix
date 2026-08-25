; Exercises fixed-width arithmetic, bitwise operations, shifts, casts, and
; every signed and unsigned integer comparison predicate on non-constant IR.

declare void @__assert_fail()
declare i8 @nondet_i8()
declare void @observe_i1(i1)
declare void @observe_i8(i8)
declare void @observe_i16(i16)

define i32 @main() {
entry:
  %x = call i8 @nondet_i8()
  %y = call i8 @nondet_i8()
  %nonzero_y = or i8 %y, 1

  %sub = sub i8 %x, %y
  %add = add i8 %sub, %y
  call void @observe_i8(i8 %add)
  call void @observe_i8(i8 %sub)
  %add_sub_ok = icmp eq i8 %add, %x
  %mul = mul i8 %x, 2
  %shl = shl i8 %x, 1
  call void @observe_i8(i8 %mul)
  call void @observe_i8(i8 %shl)
  %mul_shl_ok = icmp eq i8 %mul, %shl
  %udiv = udiv i8 %x, %nonzero_y
  %urem = urem i8 %x, %nonzero_y
  %urebuild_mul = mul i8 %udiv, %nonzero_y
  %urebuild = add i8 %urebuild_mul, %urem
  call void @observe_i8(i8 %udiv)
  call void @observe_i8(i8 %urem)
  %udiv_rem_ok = icmp eq i8 %urebuild, %x
  %sdiv = sdiv i8 %x, 2
  %srem = srem i8 %x, 2
  %srebuild_mul = mul i8 %sdiv, 2
  %srebuild = add i8 %srebuild_mul, %srem
  call void @observe_i8(i8 %sdiv)
  call void @observe_i8(i8 %srem)
  %sdiv_rem_ok = icmp eq i8 %srebuild, %x

  %bit_and = and i8 %x, %y
  %bit_xor = xor i8 %x, %y
  %bit_or = or i8 %bit_and, %bit_xor
  %expected_or = or i8 %x, %y
  call void @observe_i8(i8 %bit_and)
  call void @observe_i8(i8 %bit_or)
  call void @observe_i8(i8 %bit_xor)
  %bitwise_ok = icmp eq i8 %bit_or, %expected_or
  %lshr = lshr i8 %x, 1
  call void @observe_i8(i8 %lshr)
  %lshr_ok = icmp ule i8 %lshr, 127
  %ashr = ashr i8 %x, 1
  call void @observe_i8(i8 %ashr)
  %ashr_low_ok = icmp sge i8 %ashr, -64
  %ashr_high_ok = icmp sle i8 %ashr, 63

  %zext = zext i8 %x to i16
  call void @observe_i16(i16 %zext)
  %wide = add i16 %zext, 1
  %zext_back = trunc i16 %wide to i8
  call void @observe_i16(i16 %wide)
  call void @observe_i8(i8 %zext_back)
  %incremented_x = add i8 %x, 1
  %zext_ok = icmp eq i8 %zext_back, %incremented_x
  %sext = sext i8 %x to i16
  call void @observe_i16(i16 %sext)
  %sext_back = trunc i16 %sext to i8
  %sext_ok = icmp eq i8 %sext_back, %x
  %trunc_bool = trunc i8 %x to i1
  call void @observe_i1(i1 %trunc_bool)
  %bool_as_byte = zext i1 %trunc_bool to i8
  %low_bit = and i8 %x, 1
  %trunc_bool_ok = icmp eq i8 %bool_as_byte, %low_bit

  %eq = icmp eq i8 %x, %y
  %ne = icmp ne i8 %x, %y
  %ugt = icmp ugt i8 %x, %y
  %uge = icmp uge i8 %x, %y
  %ult = icmp ult i8 %x, %y
  %ule = icmp ule i8 %x, %y
  %sgt = icmp sgt i8 %x, %y
  %sge = icmp sge i8 %x, %y
  %slt = icmp slt i8 %x, %y
  %sle = icmp sle i8 %x, %y
  call void @observe_i1(i1 %eq)
  call void @observe_i1(i1 %ne)
  call void @observe_i1(i1 %ugt)
  call void @observe_i1(i1 %uge)
  call void @observe_i1(i1 %ult)
  call void @observe_i1(i1 %ule)
  call void @observe_i1(i1 %sgt)
  call void @observe_i1(i1 %sge)
  call void @observe_i1(i1 %slt)
  call void @observe_i1(i1 %sle)
  %not_eq = xor i1 %eq, true
  %not_ne = xor i1 %ne, true
  %not_ugt = xor i1 %ugt, true
  %not_uge = xor i1 %uge, true
  %not_ult = xor i1 %ult, true
  %not_ule = xor i1 %ule, true
  %not_sgt = xor i1 %sgt, true
  %not_sge = xor i1 %sge, true
  %not_slt = xor i1 %slt, true
  %not_sle = xor i1 %sle, true
  %eq_tautology = or i1 %eq, %not_eq
  %ne_tautology = or i1 %ne, %not_ne
  %ugt_tautology = or i1 %ugt, %not_ugt
  %uge_tautology = or i1 %uge, %not_uge
  %ult_tautology = or i1 %ult, %not_ult
  %ule_tautology = or i1 %ule, %not_ule
  %sgt_tautology = or i1 %sgt, %not_sgt
  %sge_tautology = or i1 %sge, %not_sge
  %slt_tautology = or i1 %slt, %not_slt
  %sle_tautology = or i1 %sle, %not_sle

  %all1 = and i1 %add_sub_ok, %mul_shl_ok
  %all2 = and i1 %all1, %udiv_rem_ok
  %all3 = and i1 %all2, %sdiv_rem_ok
  %all4 = and i1 %all3, %bitwise_ok
  %all5 = and i1 %all4, %lshr_ok
  %all6 = and i1 %all5, %ashr_low_ok
  %all7 = and i1 %all6, %ashr_high_ok
  %all8 = and i1 %all7, %zext_ok
  %all9 = and i1 %all8, %sext_ok
  %all10 = and i1 %all9, %trunc_bool_ok
  %all11 = and i1 %all10, %eq_tautology
  %all12 = and i1 %all11, %ne_tautology
  %all13 = and i1 %all12, %ugt_tautology
  %all14 = and i1 %all13, %uge_tautology
  %all15 = and i1 %all14, %ult_tautology
  %all16 = and i1 %all15, %ule_tautology
  %all17 = and i1 %all16, %sgt_tautology
  %all18 = and i1 %all17, %sge_tautology
  %all19 = and i1 %all18, %slt_tautology
  %all20 = and i1 %all19, %sle_tautology
  br i1 %all20, label %safe, label %error

safe:
  ret i32 0

error:
  call void @__assert_fail()
  unreachable
}
