needs "Multivariate/realanalysis.ml";;
needs "Cnu/matrixanalysis.ml";;
needs "Cnu/pp.ml";;
needs "Cnu/robotic_dynamic.ml";;
needs "Cnu/finial.ml";;

(* ------------------------------------------------------------------------- *)
(* Kinematic equations of the single-sphere driven balance robot.            *)
(* ------------------------------------------------------------------------- *)

let gsb_mul_gbt =prove
 (`! gsb gbt gst pbt Rst psb  pst Rbt Rsb t l.
  gsb = (\t. homo_trans (psb t) (Rsb t)) /\
  gbt = (\t. homo_trans (pbt t) (Rbt t)) /\
  pbt = (\t. l %% (Rbt t) ** (basis 3))/\
  Rst = (\t. (Rsb t) ** (Rbt t))/\
  gst = (\t. gsb(t) ** gbt(t))
  ==> gst = (\t. homo_trans (psb t + Rsb t ** l %% Rbt t ** basis 3) (Rst t))`,
  SIMP_TAC[HOMO_TRANS_MUL_TRANS]);;

let spatial_velocity_ballbot = prove
 (`!g R R' t l. (!t. rotation_matrix (R t))/\
  (R has_v1matrix_derivative (R' t) ) (at t) /\
  g = (\t. homo_trans ((l %% (R t)) ** (basis 3)) (R t))
  ==> spatial_velocity g UNIV t = twist_wedge (pastecart (vec 0 : real^3) (matrix3_vee(spatial_velocity R UNIV t)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[spatial_velocity] THEN
  SUBGOAL_THEN
  `v1matrix_derivative R (at t within (:real^1)) = (R' (t:real^1)):real^3^3 `
  ASSUME_TAC THENL
  [REWRITE_TAC[WITHIN_UNIV] THEN MATCH_MP_TAC V1MATRIX_DERIVATIVE_AT THEN
  ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
  `matrix_inv (R (t:real^1):real^3^3) = transp (R (t:real^1):real^3^3)`
  ASSUME_TAC THENL
  [ASM_SIMP_TAC[ROTATION_MATRIX_INV];ALL_TAC] THEN
  SUBGOAL_THEN
  `v1matrix_derivative g (at t within (:real^1))
  = homo_matrix ((R' t):real^3^3) ((l %% (R' t)) ** (basis 3)) (vec 0) (&0)`
  SUBST1_TAC THENL
  [REWRITE_TAC[WITHIN_UNIV] THEN MATCH_MP_TAC V1MATRIX_DERIVATIVE_AT THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_HOMO_TRANS_AT THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
  `l %% ((R' t) :real^3^3) ** basis 3 =
  l %% (R(t :real^1) :real^3^3) ** vec 0 + l %% (R' t) ** (basis 3) `
  SUBST1_TAC THENL
  [REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_LID];ALL_TAC] THEN
  MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_MATRIX_VECTOR_MUL_AT THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[];
  REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]]; ALL_TAC] THEN
  SUBGOAL_THEN
  `matrix_inv (g (t:real^1)) =
  homo_matrix (transp(R t):real^3^3) (--l % (basis 3)) (vec 0) (&1)`
  SUBST1_TAC THENL
  [MP_TAC(ISPECL[`l %% (R (t:real^1) :real^3^3) ** basis 3 :real^3`;
                  `R (t:real^1):real^3^3`;
                 ] MATRIX_INV_HOMO_TRANS) THEN
  ASM_SIMP_TAC[ROTATION_MATRIX_INVERTIBLE] THEN STRIP_TAC THEN
  REWRITE_TAC[HOMO_MATRIX_UNIQUE;homo_trans] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_RMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL;MATRIX_VECTOR_MUL_LID;
               VECTOR_MUL_ASSOC;MATRIX_NEG_MINUS1;MATRIX_MUL_LMUL] THEN
  UNDISCH_TAC`!t. rotation_matrix (R (t:real^1):real^3^3)` THEN
  SIMP_TAC[rotation_matrix;orthogonal_matrix] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1] ; ALL_TAC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM homo_trans;HOMO_MATRIX_ZERO_MUL_HOMO_TRANS;
              twist_wedge;SNDCART_PASTECART;FSTCART_PASTECART] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL;MATRIX_VECTOR_LMUL;HOMO_MATRIX_UNIQUE] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC (GSYM VEC3_2_SSM_MATRIX3_VEE) THEN
  SUBGOAL_THEN
  `(R' (t:real^1) :real^3^3) ** transp (R (t:real^1) :real^3^3) = (spatial_velocity R UNIV t)`
  ASSUME_TAC THENL[REWRITE_TAC[spatial_velocity] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
  `(R:real^1->real^3^3) vmatrix_differentiable (at (t:real^1))`
  ASSUME_TAC THENL[ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE THEN
  EXISTS_TAC `R' (t:real^1): real^3^3` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ANGULER_VELOCITY_MATRIX_SSM];
  VECTOR_ARITH_TAC]);;

let dpst_ballbot = prove
 (`!Rsb Rbt Rst (Rsb)' (Rbt)' psb pbt gsb gbt gst wsb vsb wbt vbt vst wst t.
  (!t. rotation_matrix (Rsb t))/\
  (!t. rotation_matrix (Rbt t))/\
  (Rsb has_v1matrix_derivative (Rsb' t) ) (at t) /\
  (Rbt has_v1matrix_derivative (Rbt' t) ) (at t) /\
  (psb has_vector_derivative (psb' t)) (at t) /\
  Rst = (\t. (Rsb t) ** (Rbt t))/\
  pbt = (\t. l %% (Rbt t) ** (basis 3)) /\
  gsb = (\t. homo_trans (psb t) (Rsb t)) /\
  gbt = (\t. homo_trans (pbt t) (Rbt t)) /\
  gst = (\t. homo_trans (pst t) (Rst t)) /\
  vsb = homo_matrix_snd(spatial_velocity gsb UNIV t) /\
  wsb = matrix3_vee(homo_matrix_fst(spatial_velocity gsb UNIV t)) /\
  vbt = homo_matrix_snd(spatial_velocity gbt UNIV t)  /\
  wbt = matrix3_vee(homo_matrix_fst(spatial_velocity gbt UNIV t))  /\
  gst = (\t. gsb(t) ** gbt(t)) /\
  pst = (\t. psb t + (Rsb t :real^3^3) ** (l %% (Rbt t :real^3^3)) ** basis 3)/\
  vst = homo_matrix_snd(spatial_velocity gst UNIV t) /\
  wst = matrix3_vee(homo_matrix_fst(spatial_velocity gst UNIV t))
  ==> gst = (\t. homo_trans (psb t + Rsb t ** l %% Rbt t ** basis 3) (Rst t))/\
      vector_derivative pst (at t) = vector_derivative psb (at t) + l % wst cross (Rst t ** (basis 3))`,
  INTRO_TAC "! * ; rotRsb rotRbt Rsbdif Rbtdif psb' Rst pbt gsb gbt gst1 vsb wsb vbt wbt gst2 pst vst wst" THEN
  CLAIM_TAC "l_mul_dRbt_mul_b3"
  `l %% ((Rbt' t) :real^3^3) ** basis 3 = l %% (Rbt(t :real^1) :real^3^3) ** vec 0 + l %% (Rbt' t) ** (basis 3)`
  THENL [REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_LID];ALL_TAC] THEN
  CLAIM_TAC "d_l_mul_Rbt"
  `((\t. l %% (Rbt (t:real^1) :real^3^3)) has_v1matrix_derivative (l %% Rbt' t)) (at t)` THENL [MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[] ;ALL_TAC] THEN
  CLAIM_TAC "v1m_dRbt"
  `v1matrix_derivative Rbt (at t within (:real^1)) = Rbt' t:real^3^3`
  THENL[REWRITE_TAC[WITHIN_UNIV] THEN MATCH_MP_TAC V1MATRIX_DERIVATIVE_AT THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `pbt' = (\t:real^1. l %% ((Rbt' t):real^3^3) ** (basis 3))` THEN
  CLAIM_TAC "pbt_hvd" `((pbt :real^1->real^3) has_vector_derivative pbt' t) (at t)`
  THENL [ASM_SIMP_TAC[] THEN EXPAND_TAC "pbt'" THEN
  SUBGOAL_THEN
  `l %% ((Rbt' t) :real^3^3) ** basis 3 = l %% (Rbt(t :real^1) :real^3^3) ** vec 0 + l %% (Rbt' t) ** (basis 3)`
  SUBST1_TAC THENL [REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_LID];ALL_TAC] THEN
  SUBGOAL_THEN `((\t. (basis 3 :real^3) ) has_vector_derivative (vec 0)) (at t)`
  ASSUME_TAC THENL [REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] ;ALL_TAC] THEN
  MP_TAC(ISPECL[`\t:real^1. l %% Rbt t :real^3^3`; `\t:real^1. basis 3 :real^3`;
                `\t:real^1. l %% Rbt' t :real^3^3`; `\t:real^1. vec 0 :real^3`;
                `t:real^1`] HAS_V1MATRIX_DERIVATIVE_MATRIX_VECTOR_MUL_AT) THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  ABBREV_TAC `pst'= (\t:real^1. ((psb' t):real^3) + (((Rsb t):real^3^3) ** (l %% ((Rbt' t):real^3^3)) ** ((basis 3):real^3) + ((Rsb' t):real^3^3) ** (l %% ((Rbt t):real^3^3)) ** ((basis 3):real^3)))` THEN
  CLAIM_TAC "psthvd" `((\t:real^1. (pst t:real^3)) has_vector_derivative pst' t) (at t)` THENL [HYP SIMP_TAC "pst"[] THEN EXPAND_TAC "pst'" THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_MATRIX_VECTOR_MUL_AT THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `l %% ((Rbt' t) :real^3^3) ** basis 3 = l %% (Rbt(t :real^1) :real^3^3) ** vec 0 + l %% (Rbt' t) ** (basis 3)`
  SUBST1_TAC THENL [REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_LID];ALL_TAC] THEN
  SUBGOAL_THEN `((\t. (basis 3 :real^3) ) has_vector_derivative (vec 0)) (at t)`
  ASSUME_TAC THENL [REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST] ;ALL_TAC] THEN
  MP_TAC(ISPECL[`\t:real^1. l %% Rbt t :real^3^3`; `\t:real^1. basis 3 :real^3`;
                `\t:real^1. l %% Rbt' t :real^3^3`; `\t:real^1. vec 0 :real^3`;
               `t:real^1`] HAS_V1MATRIX_DERIVATIVE_MATRIX_VECTOR_MUL_AT) THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[ETA_AX];ALL_TAC] THEN
  ABBREV_TAC `Rst' = (\t:real^1. ((Rsb t):real^3^3) ** ((Rbt' t):real^3^3)  + ((Rsb' t):real^3^3) ** ((Rbt t):real^3^3))` THEN
  CLAIM_TAC "Rstv1md" `((\t.(Rst (t:real^1) :real^3^3)) has_v1matrix_derivative  Rst' t) (at t)` THENL [ASM_SIMP_TAC[] THEN EXPAND_TAC "Rst'" THEN MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_MATRIX_MUL_AT THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CLAIM_TAC "RotRst" `!t:real^1. rotation_matrix (Rst t :real^3^3)` THENL [
  GEN_TAC THEN ASM_SIMP_TAC[rotation_matrix] THEN CONJ_TAC THENL[ MATCH_MP_TAC ORTHOGONAL_MATRIX_MUL THEN ASM_MESON_TAC[rotation_matrix];ALL_TAC] THEN  REWRITE_TAC[DET_MUL] THEN ASM_MESON_TAC[rotation_matrix;REAL_MUL_LID];ALL_TAC] THEN
  CLAIM_TAC "InvRst" `!t:real^1. invertible (Rst t :real^3^3)` THENL [ASM_SIMP_TAC[ROTATION_MATRIX_INVERTIBLE];ALL_TAC] THEN
  CLAIM_TAC "svgbt" `spatial_velocity gbt UNIV t = twist_wedge (pastecart (vec 0) (matrix3_vee(spatial_velocity Rbt UNIV t)))` THENL
  [REWRITE_TAC[spatial_velocity] THEN
  SUBGOAL_THEN`matrix_inv (Rbt (t:real^1):real^3^3) = transp (Rbt t)`ASSUME_TAC THENL
  [ASM_SIMP_TAC[ROTATION_MATRIX_INV];ALL_TAC] THEN
  SUBGOAL_THEN `v1matrix_derivative gbt (at t within (:real^1)) = homo_matrix ((Rbt' t):real^3^3) ((l %% (Rbt' t)) ** basis 3) (vec 0) (&0)`
  SUBST1_TAC THENL [REWRITE_TAC[WITHIN_UNIV] THEN MATCH_MP_TAC V1MATRIX_DERIVATIVE_AT THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_HOMO_TRANS_AT THEN
  ASM_SIMP_TAC[] THEN SUBGOAL_THEN `l %% (Rbt' (t:real^1) :real^3^3) ** basis 3 = l %% (Rbt t :real^3^3) ** vec 0 + l %% (Rbt' t) ** (basis 3) ` SUBST1_TAC THENL
  [REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO;VECTOR_ADD_LID];ALL_TAC] THEN
  MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_MATRIX_VECTOR_MUL_AT THEN CONJ_TAC THENL
  [MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[];REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]]; ALL_TAC] THEN
  SUBGOAL_THEN `matrix_inv (gbt (t:real^1)) = homo_matrix (transp(Rbt t):real^3^3) (--l % (basis 3)) (vec 0) (&1)`
  SUBST1_TAC THENL
  [MP_TAC(ISPECL[`l %% (Rbt (t:real^1) :real^3^3) ** basis 3 :real^3`;`Rbt(t:real^1):real^3^3`;] MATRIX_INV_HOMO_TRANS) THEN
  ASM_SIMP_TAC[ROTATION_MATRIX_INVERTIBLE] THEN STRIP_TAC THEN
  REWRITE_TAC[HOMO_MATRIX_UNIQUE;homo_trans] THEN
  ASM_SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC;MATRIX_MUL_RMUL] THEN
  REWRITE_TAC[MATRIX_VECTOR_LMUL;MATRIX_VECTOR_MUL_LID;VECTOR_MUL_ASSOC;MATRIX_NEG_MINUS1;MATRIX_MUL_LMUL] THEN UNDISCH_TAC`!t. rotation_matrix (Rbt (t:real^1):real^3^3)` THEN SIMP_TAC[rotation_matrix;orthogonal_matrix] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LID] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  REWRITE_TAC[GSYM REAL_NEG_MINUS1] ; ALL_TAC] THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM homo_trans;HOMO_MATRIX_ZERO_MUL_HOMO_TRANS;twist_wedge;
  SNDCART_PASTECART;FSTCART_PASTECART] THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_RMUL;MATRIX_VECTOR_LMUL;HOMO_MATRIX_UNIQUE] THEN
  CONJ_TAC THENL [MATCH_MP_TAC (GSYM VEC3_2_SSM_MATRIX3_VEE) THEN
  SUBGOAL_THEN `(Rbt' (t:real^1) :real^3^3) ** transp (Rbt t) = (spatial_velocity Rbt UNIV t)`
  ASSUME_TAC THENL[REWRITE_TAC[spatial_velocity] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(Rbt:real^1->real^3^3) vmatrix_differentiable (at t)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE THEN
  EXISTS_TAC `Rbt' (t:real^1): real^3^3` THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[ANGULER_VELOCITY_MATRIX_SSM];VECTOR_ARITH_TAC];ALL_TAC] THEN
  CONJ_TAC THENL [HYP SIMP_TAC "gst2"[] THEN ASM_SIMP_TAC[] THEN REWRITE_TAC[HOMO_TRANS_MUL_TRANS] ;ALL_TAC] THEN
  CLAIM_TAC "mtrveevstwst" `matrix4_vee(spatial_velocity
  (\t. (homo_trans (psb t) (Rsb t)) ** (homo_trans (pbt t) (Rbt t))) UNIV t)
  = matrix4_vee(spatial_velocity (\t. homo_trans (psb t) (Rsb t)) UNIV t) +
  ad_trans(homo_trans (psb t) (Rsb t)) ** matrix4_vee(spatial_velocity (\t. homo_trans (pbt t) (Rbt t)) UNIV t)`
  THENL [
  MP_TAC(ISPECL[`Rsb:real^1->real^3^3`;`Rbt:real^1->real^3^3`;
                `Rsb' (t:real^1) :real^3^3`;`Rbt' (t:real^1) :real^3^3`;
                `psb :real^1->real^3`;`pbt :real^1->real^3`;
                `psb' (t:real^1) :real^3`;`pbt' (t:real^1) :real^3 `;
                `t:real^1`] MATRIX4_VEE_SPATIAL_VELOCITY_HOMO_TRANS_MUL) THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CLAIM_TAC "svgst"
  `spatial_velocity (gst:real^1->real^(3,1)finite_sum^(3,1)finite_sum) (:real^1) t =
  ((homo_matrix (vec3_2_ssm(wst):real^3^3) (vst:real^3) (vec 0:real^3) (&0)))`
  THENL [HYP SIMP_TAC "wst vst gst1" []  THEN
  MP_TAC(ISPECL[`\t:real^1. pst t:real^3`;`\t:real^1.Rst t :real^3^3`;
                `pst' (t:real^1) :real^3`;`Rst' (t:real^1) :real^3^3`;
                `t:real^1`] SPATIAL_VELOCITY) THEN HYP SIMP_TAC "InvRst Rstv1md psthvd" [] THEN DISCH_TAC THEN
  REWRITE_TAC[HOMO_MATRIX_FST_HOMO_MATRIX;HOMO_MATRIX_SND_HOMO_MATRIX;
  HOMO_MATRIX_UNIQUE] THEN
  CLAIM_TAC "Rstvmd" `(\t. (Rst (t:real^1) :real^3^3)) vmatrix_differentiable (at t)` THENL[ MP_TAC(ISPECL[`\t:real^1.Rst t :real^3^3 `;`Rst' (t:real^1) :real^3^3`] HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE)
  THEN HYP SIMP_TAC "Rstv1md" [];ALL_TAC] THEN
  CLAIM_TAC "ssm_svRst" `matrix_ssm (spatial_velocity (Rst :real^1->real^3^3) UNIV t)` THENL [MP_TAC(ISPECL[`\t:real^1.Rst t :real^3^3 `;`t:real^1`] ANGULER_VELOCITY_MATRIX_SSM) THEN
  HYP SIMP_TAC "RotRst Rstvmd"[] THEN REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[spatial_velocity] THEN
  CLAIM_TAC "Rstv1md2" `((Rst :real^1->real^3^3) has_v1matrix_derivative  Rst'(t)) (at t)` THENL [HYP SIMP_TAC "Rst"[] THEN EXPAND_TAC "Rst'" THEN MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_MATRIX_MUL_AT THEN HYP SIMP_TAC "Rsbdif Rbtdif"[];ALL_TAC] THEN
  CLAIM_TAC "v1mdev" `v1matrix_derivative (Rst :real^1->real^3^3) (at t) = Rst' (t:real^1):real^3^3` THENL[
  MP_TAC(ISPECL[`\t:real^1. Rst (t:real^1):real^3^3`;`Rst' (t:real^1):real^3^3`;`t:real^1`] V1MATRIX_DERIVATIVE_AT) THEN REWRITE_TAC[ETA_AX] THEN
  HYP SIMP_TAC "Rstv1md2"[];ALL_TAC] THEN REWRITE_TAC[WITHIN_UNIV] THEN HYP SIMP_TAC "v1mdev"[] THEN SIMP_TAC[VEC3_2_SSM_MATRIX3_VEE];ALL_TAC] THEN
  CLAIM_TAC "mtr4vee_sv_gst2" ` pastecart vst wst= matrix4_vee (spatial_velocity gst UNIV t)`
  THENL [HYP SIMP_TAC "svgst"[] THEN CLAIM_TAC "mtr_ssm_wst" `matrix_ssm (vec3_2_ssm wst)` THENL  [SIMP_TAC[MATRIX_SSM_VEC3_2_SSM];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[MATRIX4_VEE_HOMO_MATRIX;MATRIX3_VEE_VEC3_2_SSM];ALL_TAC] THEN
  CLAIM_TAC "pstc_vsb2_wsb2"
  `pastecart vsb wsb= matrix4_vee (spatial_velocity gsb (:real^1) t)` THENL
  [HYP SIMP_TAC "vsb wsb gsb" [] THEN
  MP_TAC(ISPECL[`psb :real^1->real^3`; `Rsb :real^1->real^3^3`;`psb' (t:real^1):real^3`;
                `Rsb'(t:real^1):real^3^3`;`t:real^1`] SPATIAL_VELOCITY) THEN
  HYP SIMP_TAC "Rsbdif psb'"[] THEN
  CLAIM_TAC "invRsb" `!t:real^1. invertible (Rsb t :real^3^3)` THENL [ASM_SIMP_TAC[ROTATION_MATRIX_INVERTIBLE];ALL_TAC] THEN HYP SIMP_TAC "invRsb"[] THEN DISCH_TAC
  THEN SIMP_TAC[HOMO_MATRIX_FST_HOMO_MATRIX;HOMO_MATRIX_SND_HOMO_MATRIX] THEN
  CLAIM_TAC "ssm_svRsb" `matrix_ssm (spatial_velocity (Rsb :real^1->real^3^3) UNIV t)` THENL[MP_TAC(ISPECL[`\t:real^1.Rsb t :real^3^3 `; `t:real^1`] ANGULER_VELOCITY_MATRIX_SSM) THEN
  CLAIM_TAC "Rsbvmd" `(\t. (Rsb (t:real^1) :real^3^3)) vmatrix_differentiable (at t)` THENL[
  MP_TAC(ISPECL[`\t:real^1.Rsb t :real^3^3 `;`Rsb' (t:real^1) :real^3^3 `] HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE)
  THEN REWRITE_TAC[ETA_AX] THEN HYP SIMP_TAC "Rsbdif" [];ALL_TAC] THEN
  HYP SIMP_TAC "rotRsb Rsbvmd"[] THEN REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[spatial_velocity] THEN
  CLAIM_TAC "v1mdevRsb" `v1matrix_derivative (Rsb :real^1->real^3^3) (at t) = Rsb' t` THENL[
  MP_TAC(ISPECL[`\t:real^1. Rsb (t:real^1):real^3^3`; `Rsb' (t:real^1):real^3^3`;
                `t:real^1`] V1MATRIX_DERIVATIVE_AT) THEN REWRITE_TAC[ETA_AX] THEN
  HYP SIMP_TAC "Rsbdif"[];ALL_TAC] THEN REWRITE_TAC[WITHIN_UNIV] THEN HYP SIMP_TAC "v1mdevRsb"[] THEN SIMP_TAC[MATRIX4_VEE_HOMO_MATRIX];ALL_TAC] THEN
  CLAIM_TAC "pstc_vbt_wbt"
  `pastecart vbt wbt= matrix4_vee (spatial_velocity gbt (:real^1) t)` THENL[
  HYP SIMP_TAC "vbt wbt gbt" [] THEN
  MP_TAC(ISPECL[`pbt :real^1->real^3`; `Rbt :real^1->real^3^3`;`pbt' (t:real^1):real^3`;
                `Rbt'(t:real^1):real^3^3`;`t:real^1`] SPATIAL_VELOCITY) THEN
  HYP SIMP_TAC "Rbtdif pbt_hvd"[] THEN
  CLAIM_TAC "invRbt" `!t:real^1. invertible (Rbt t :real^3^3)` THENL [ASM_SIMP_TAC[ROTATION_MATRIX_INVERTIBLE];ALL_TAC] THEN HYP SIMP_TAC "invRbt"[] THEN DISCH_TAC THEN SIMP_TAC[HOMO_MATRIX_FST_HOMO_MATRIX;HOMO_MATRIX_SND_HOMO_MATRIX] THEN
  CLAIM_TAC "ssm_svRbt" `matrix_ssm (spatial_velocity (Rbt :real^1->real^3^3) UNIV t)` THENL[MP_TAC(ISPECL[`\t:real^1.Rbt t :real^3^3 `;`t:real^1`] ANGULER_VELOCITY_MATRIX_SSM) THEN
  CLAIM_TAC "Rbtvmd" `(\t. (Rbt (t:real^1) :real^3^3)) vmatrix_differentiable (at t)` THENL[
  MP_TAC(ISPECL[`\t:real^1.Rbt t :real^3^3 `;`Rbt' (t:real^1) :real^3^3`] HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE)
  THEN REWRITE_TAC[ETA_AX] THEN HYP SIMP_TAC "Rbtdif" [];ALL_TAC] THEN HYP SIMP_TAC "rotRbt Rbtvmd"[] THEN REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[spatial_velocity] THEN
  CLAIM_TAC "v1mdevRbt" `v1matrix_derivative (Rbt :real^1->real^3^3) (at t) = Rbt' t` THENL[
  MP_TAC(ISPECL[`\t:real^1. Rbt (t:real^1):real^3^3`; `Rbt' (t:real^1):real^3^3`;`t:real^1`] V1MATRIX_DERIVATIVE_AT) THEN REWRITE_TAC[ETA_AX] THEN
  HYP SIMP_TAC "Rbtdif"[];ALL_TAC] THEN REWRITE_TAC[WITHIN_UNIV] THEN HYP SIMP_TAC "v1mdevRbt"[] THEN SIMP_TAC[MATRIX4_VEE_HOMO_MATRIX];ALL_TAC] THEN
  CLAIM_TAC "Adgsb_vwbt"
  `pastecart (Rsb t ** fstcart (pastecart (vbt:real^3) (wbt:real^3)) +
  (vec3_2_ssm (psb (t:real^1):real^3) ** Rsb t) ** sndcart (pastecart (vbt) (wbt))) ((mat 0) ** fstcart (pastecart (vbt) (wbt)) + Rsb t ** sndcart (pastecart (vbt) (wbt))) = ad_trans (homo_trans (psb t) (Rsb (t:real^1):real^3^3) ) ** (pastecart (vbt) (wbt))` THENL[REWRITE_TAC[AD_TRANS_HOMO_TRANS;BLOCKMATRIX_VECTOR_MUL];ALL_TAC] THEN
  CLAIM_TAC "patc_vsb_wsb_addbt"
  `pastecart (vsb:real^3) (wsb:real^3) + pastecart ((Rsb (t:real^1):real^3^3)** fstcart (pastecart (vbt:real^3) (wbt:real^3)) +(vec3_2_ssm (psb (t:real^1):real^3) ** (Rsb t)) ** sndcart (pastecart (vbt) (wbt:real^3)))(mat 0 ** fstcart (pastecart vbt wbt) +Rsb t ** sndcart (pastecart vbt wbt)) = pastecart (vsb + (Rsb t ** fstcart (pastecart vbt wbt) + (vec3_2_ssm (psb t) ** Rsb t) ** sndcart (pastecart vbt wbt))) (wsb + (mat 0 ** fstcart (pastecart vbt wbt) +Rsb t ** sndcart (pastecart vbt wbt)))` THENL[SIMP_TAC[PASTECART_ADD];ALL_TAC ] THEN
  CLAIM_TAC "patc_vst_wst"
  `(pastecart (vst:real^3) (wst:real^3)) = (pastecart (vsb:real^3) (wsb:real^3)) +
  (pastecart ((Rsb (t:real^1):real^3^3) ** fstcart (pastecart (vbt:real^3) (wbt:real^3)) +
  (vec3_2_ssm (psb (t:real^1):real^3) ** Rsb t) ** sndcart (pastecart (vbt) (wbt)))
  ((mat 0) ** fstcart (pastecart (vbt) (wbt)) + (Rsb t) ** sndcart (pastecart (vbt) (wbt))))`THENL [HYP SIMP_TAC "mtr4vee_sv_gst2 pstc_vsb2_wsb2 Adgsb_vwbt gst2 gsb pstc_vbt_wbt gbt mtrveevstwst"[] THEN HYP SIMP_TAC "patc_vst_wst"[];ALL_TAC]
  THEN HYP SIMP_TAC "patc_vsb_wsb_addbt patc_vst_wst"[] THEN
  CLAIM_TAC "vst_eq_vsb_add"
  `vst = (vsb:real^3) + psb t cross ((Rsb (t:real^1):real^3^3) ** (wbt:real^3))`
  THENL[POP_ASSUM MP_TAC THEN REWRITE_TAC[PASTECART_ADD;PASTECART_INJ] THEN
  REWRITE_TAC[FSTCART_PASTECART;SNDCART_PASTECART] THEN REWRITE_TAC[CROSS_SSM] THEN
  CLAIM_TAC "mat4_v_sv_gbt"
  `matrix4_vee(spatial_velocity gbt (:real^1) t) =matrix4_vee (twist_wedge
  (pastecart (vec 0) (matrix3_vee (spatial_velocity Rbt (:real^1) t))))` THENL
  [HYP SIMP_TAC "svgbt"[];ALL_TAC] THEN
  CLAIM_TAC "past_vw_eq"
  `pastecart (vbt:real^3) (wbt:real^3) = (pastecart (vec 0) (matrix3_vee (spatial_velocity Rbt (:real^1) t)))` THENL[HYP SIMP_TAC "pstc_vbt_wbt"[] THEN HYP REWRITE_TAC "mat4_v_sv_gbt"[] THEN SIMP_TAC[MATRIX4_VEE_TWIST_WEDGE] ;ALL_TAC] THEN
  CLAIM_TAC "vbt_eq_0"
  `(vbt:real^3 )= (vec 0:real^3)`THENL[POP_ASSUM MP_TAC THEN SIMP_TAC[PASTECART_INJ];ALL_TAC] THEN
  HYP SIMP_TAC "vbt_eq_0"[] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN REWRITE_TAC[VECTOR_ADD_LID]
  THEN SIMP_TAC[MATRIX_VECTOR_MUL_ASSOC];ALL_TAC] THEN
  CLAIM_TAC "wst_eq_wsb_add"
  `wst = wsb + (Rsb (t:real^1):real^3^3) ** (wbt:real^3)`
  THENL [UNDISCH_TAC `pastecart vst wst =
  pastecart (vsb:real^3) (wsb:real^3) +pastecart((Rsb (t:real^1):real^3^3) ** fstcart (pastecart (vbt:real^3) (wbt:real^3)) +(vec3_2_ssm (psb t :real^3) ** (Rsb t :real^3^3)) ** sndcart (pastecart vbt wbt))(mat 0 ** fstcart (pastecart vbt wbt) +Rsb t ** sndcart (pastecart vbt wbt))` THEN REWRITE_TAC[PASTECART_ADD;PASTECART_INJ] THEN REWRITE_TAC[FSTCART_PASTECART;SNDCART_PASTECART] THEN REWRITE_TAC[CROSS_SSM] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO] THEN SIMP_TAC[VECTOR_ADD_LID];ALL_TAC] THEN
  CLAIM_TAC "vd_pst"
  `vector_derivative (pst) (at t) = vst +(wst cross pst t)` THENL [UNDISCH_TAC `pastecart vst wst = matrix4_vee (spatial_velocity gst (:real^1) t)` THEN HYP SIMP_TAC "gst1"[] THEN
  MP_TAC(ISPECL[`\t:real^1. pst t:real^3`;`\t:real^1.Rst t :real^3^3`;
                `pst' (t:real^1) :real^3`;`Rst' (t:real^1) :real^3^3`;`t:real^1`] SPATIAL_VELOCITY) THEN HYP SIMP_TAC "InvRst Rstv1md psthvd" [] THEN
  DISCH_TAC THEN CLAIM_TAC "Rstvmd" `(\t. (Rst (t:real^1) :real^3^3)) vmatrix_differentiable (at t)` THENL[
  MP_TAC(ISPECL[`\t:real^1.Rst t :real^3^3 `;`Rst' (t:real^1) :real^3^3 `] HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE)THEN HYP SIMP_TAC "Rstv1md" [];ALL_TAC] THEN
  CLAIM_TAC "ssm_svRst" `matrix_ssm (spatial_velocity (Rst :real^1->real^3^3) UNIV t)` THENL
  [MP_TAC(ISPECL[`\t:real^1.Rst t :real^3^3 `;
                 `t:real^1`] ANGULER_VELOCITY_MATRIX_SSM) THEN HYP SIMP_TAC "RotRst Rstvmd"[] THEN
  REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[spatial_velocity]  THEN CLAIM_TAC "Rstv1md2" `((Rst :real^1->real^3^3) has_v1matrix_derivative  Rst'(t)) (at t)` THENL [HYP SIMP_TAC "Rst"[] THEN EXPAND_TAC "Rst'" THEN MATCH_MP_TAC HAS_V1MATRIX_DERIVATIVE_MATRIX_MUL_AT THEN HYP SIMP_TAC "Rsbdif Rbtdif"[];ALL_TAC] THEN
  CLAIM_TAC "v1mdev" `v1matrix_derivative (Rst :real^1->real^3^3) (at t) = Rst' t` THENL[
  MP_TAC(ISPECL[`\t:real^1. Rst (t:real^1):real^3^3`; `Rst' (t:real^1):real^3^3`;`t:real^1`] V1MATRIX_DERIVATIVE_AT) THEN REWRITE_TAC[ETA_AX] THEN
  HYP SIMP_TAC "Rstv1md2"[];ALL_TAC] THEN REWRITE_TAC[WITHIN_UNIV] THEN HYP SIMP_TAC "v1mdev"[] THEN SIMP_TAC[MATRIX4_VEE_HOMO_MATRIX] THEN DISCH_TAC THEN REWRITE_TAC[PASTECART_INJ] THEN DISCH_TAC THEN
  CLAIM_TAC "dRst_mul_invRst"
  `(Rst' (t:real^1) :real^3^3) ** matrix_inv (Rst t) = vec3_2_ssm (wst:real^3)` THENL[POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `matrix_ssm ((Rst' (t:real^1):real^3^3) ** matrix_inv (Rst (t:real^1):real^3^3))` THEN REWRITE_TAC[GSYM VEC3_2_SSM_MATRIX3_VEE] ;ALL_TAC] THEN
  UNDISCH_TAC `vst = --((Rst' (t:real^1):real^3^3) ** matrix_inv (Rst t :real^3^3)) ** (pst t :real^3) + pst' t /\wst = matrix3_vee (Rst' t ** matrix_inv (Rst t))` THEN HYP REWRITE_TAC "dRst_mul_invRst"[] THEN REWRITE_TAC[CROSS_SSM] THEN
  CLAIM_TAC "vec_dpst"
  `vector_derivative pst (at t)=  (pst' (t:real^1) :real^3)` THENL[
  UNDISCH_TAC `((\t. pst (t:real^1) :real^3) has_vector_derivative pst' t) (at t)`
  THEN REWRITE_TAC[ETA_AX] THEN REWRITE_TAC[VECTOR_DERIVATIVE_AT] ;ALL_TAC] THEN HYP REWRITE_TAC "vec_dpst"[] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG] THEN VECTOR_ARITH_TAC;ALL_TAC] THEN
  CLAIM_TAC "vd_pst"
  `vsb = vector_derivative (psb) (at t) - (wsb cross psb t)` THENL[UNDISCH_TAC `pastecart vsb wsb = matrix4_vee (spatial_velocity gsb (:real^1) t)` THEN HYP SIMP_TAC "gsb"[] THEN
  MP_TAC(ISPECL[`\t:real^1. Rsb t:real^3^3`;`Rsb' (t:real^1) :real^3^3`;`\t:real^1. psb t:real^3`;
  `psb' (t:real^1) :real^3`;`t:real^1`] MATRIX4_VEE_SPATIAL_VELOCITY) THEN REWRITE_TAC[ETA_AX] THEN HYP SIMP_TAC "rotRsb Rsbdif psb'"[] THEN DISCH_TAC THEN
  REWRITE_TAC[PASTECART_INJ] THEN REWRITE_TAC[spatial_velocity] THEN
  CLAIM_TAC "v1m_dRsb"
  `v1matrix_derivative Rsb (at t within (:real^1)) = Rsb' t :real^3^3 `
  THENL [REWRITE_TAC[WITHIN_UNIV] THEN MATCH_MP_TAC V1MATRIX_DERIVATIVE_AT THEN
  HYP SIMP_TAC "Rsbdif"[]; ALL_TAC] THEN HYP REWRITE_TAC "v1m_dRsb"[] THEN SIMP_TAC[]  THEN DISCH_TAC THEN
  CLAIM_TAC "Rsbvmd" `(\t. (Rsb (t:real^1) :real^3^3)) vmatrix_differentiable (at t)` THENL[MP_TAC(ISPECL[`\t:real^1.Rsb t :real^3^3 `;`Rsb' (t:real^1) :real^3^3 `] HAS_V1MATRIX_DERIVATIVE_IMP_VMATRIX_DIFFERENTIABLE) THEN REWRITE_TAC[ETA_AX] THEN HYP SIMP_TAC "Rsbdif" [];ALL_TAC] THEN
  CLAIM_TAC "m_ssm_svRsb" `matrix_ssm (spatial_velocity (Rsb :real^1->real^3^3) UNIV t)` THENL [MP_TAC(ISPECL[`\t:real^1.Rsb t :real^3^3 `; `t:real^1`] ANGULER_VELOCITY_MATRIX_SSM) THEN HYP SIMP_TAC "rotRsb Rsbvmd"[] THEN
  REWRITE_TAC[ETA_AX] THEN SIMP_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[spatial_velocity] THEN HYP REWRITE_TAC "v1m_dRsb"[] THEN REWRITE_TAC[CROSS_SSM] THEN SIMP_TAC[VEC3_2_SSM_MATRIX3_VEE] THEN DISCH_TAC THEN
  CLAIM_TAC "vec_dpst"
  `vector_derivative psb (at t) = (psb' t :real^3)` THENL [MATCH_MP_TAC VECTOR_DERIVATIVE_AT THEN  HYP SIMP_TAC "psb'"[];ALL_TAC] THEN HYP SIMP_TAC "vec_dpst"[]                 THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LNEG] THEN VECTOR_ARITH_TAC ;ALL_TAC] THEN
  UNDISCH_TAC `vector_derivative pst (at t) = vst + wst cross pst t` THEN SIMP_TAC[] THEN DISCH_TAC THEN
  CLAIM_TAC "vst_mul_wst_crs_pst"
  `vst + wst cross pst t = (vsb + psb t cross ((Rsb (t:real^1):real^3^3) ** wbt)) + (wsb + Rsb t ** wbt) cross pst t` THENL [HYP SIMP_TAC "vst_eq_vsb_add wst_eq_wsb_add"[];ALL_TAC] THEN
  HYP SIMP_TAC "vst_mul_wst_crs_pst"[] THEN HYP SIMP_TAC "vd_pst"[] THEN REWRITE_TAC[CROSS_LADD] THEN REWRITE_TAC[GSYM CROSS_LADD] THEN
  CLAIM_TAC "vdpsb_sub_wsbcpsb" `vector_derivative psb (at t) - wsb cross psb t +
  psb t cross ((Rsb (t:real^1):real^3^3) ** wbt) = vector_derivative psb (at t) + psb t cross ((Rsb (t:real^1):real^3^3) ** wbt) -  wsb cross psb t` THENL[VEC3_TAC ; ALL_TAC] THEN
  HYP SIMP_TAC"vdpsb_sub_wsbcpsb"[] THEN
  CLAIM_TAC "psb_c_Rsb_mul_wbt"
  `psb t cross ((Rsb (t:real^1):real^3^3) ** (wbt:real^3)) = ((Rsb t) ** wbt) cross (-- (psb (t:real^1):real^3))` THENL[VEC3_TAC ;ALL_TAC] THEN HYP SIMP_TAC  "psb_c_Rsb_mul_wbt"[] THEN REWRITE_TAC[VECTOR_SUB] THEN REWRITE_TAC[GSYM CROSS_RNEG]  THEN REWRITE_TAC[GSYM CROSS_LADD] THEN REWRITE_TAC[VECTOR_ADD_SYM] THEN
  CLAIM_TAC "wsb_add_eq_wst"
  `(wsb:real^3 )+ (Rsb (t:real^1):real^3^3) ** (wbt:real^3) = (wst:real^3)`
  THENL [UNDISCH_TAC `pastecart vst wst =pastecart (vsb:real^3) (wsb:real^3) +pastecart
  ((Rsb (t:real^1):real^3^3) ** fstcart (pastecart (vbt:real^3) (wbt:real^3)) +
  (vec3_2_ssm (psb t :real^3) ** (Rsb t :real^3^3)) ** sndcart (pastecart vbt wbt))
  (mat 0 ** fstcart (pastecart vbt wbt) +Rsb t ** sndcart (pastecart vbt wbt))` THEN REWRITE_TAC[PASTECART_ADD;PASTECART_INJ] THEN REWRITE_TAC[FSTCART_PASTECART;SNDCART_PASTECART] THEN REWRITE_TAC[CROSS_SSM] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_LZERO] THEN SIMP_TAC[VECTOR_ADD_LID];ALL_TAC] THEN HYP SIMP_TAC "wsb_add_eq_wst"[] THEN REWRITE_TAC[VECTOR_ADD_ASSOC] THEN REWRITE_TAC[GSYM CROSS_RADD] THEN REWRITE_TAC[GSYM VECTOR_SUB] THEN HYP SIMP_TAC"pst"[] THEN
  CLAIM_TAC "psb_add_Rst"
  `((psb (t:real^1):real^3) + (Rsb t :real^3^3) ** l %% (Rbt t :real^3^3) ** basis 3) - psb t = psb t - psb t + Rsb t ** l %% Rbt t ** basis 3` THENL[VEC3_TAC;ALL_TAC] THEN HYP SIMP_TAC"psb_add_Rst"[] THEN
  REWRITE_TAC[VECTOR_SUB_REFL] THEN REWRITE_TAC[VECTOR_ADD_LID] THEN
  REWRITE_TAC[VECTOR_ADD_TEQ] THEN REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC] THEN REWRITE_TAC[MATRIX_MUL_RMUL] THEN REWRITE_TAC[CROSS_RMUL2] THEN HYP SIMP_TAC"Rst"[] THEN MAT3_TAC);;


(* ------------------------------------------------------------------------- *)
(* Dynamic equations of the single-sphere driven balance robot.              *)
(* ------------------------------------------------------------------------- *)

let BALLBOT_DYNAMICS_XOZ = prove
 (`!q t0 t1 Mt It Ib l r a b c x x' x'' theta theta' theta'' q q' q'' t.
  drop t0 < drop t1 /\ interval[t0,t1] = s /\ t IN s /\
  {u:real^(2,1)finite_sum | ?y. y IN mspace(fspace s) /\ u IN IMAGE y s} = s0 /\
  {u:real^(2,2)finite_sum | ?y. y IN mspace(fspace s) /\ u IN IMAGE y s} = s1 /\
  q = (\t. vector[drop(x t); drop(theta t)]:real^2) /\
  q'  = (\t. vector[drop(x' t); drop(theta' t)]:real^2) /\
  q'' = (\t. vector[drop(x'' t); drop(theta'' t)]:real^2) /\
  (!t. t IN s ==> (x has_vector_derivative x' t)(at t within s)) /\
  (!t. t IN s ==> (theta has_vector_derivative theta' t)(at t within s)) /\
  (!t. t IN s ==> (x' has_vector_derivative x'' t)(at t within s)) /\
  (!t. t IN s ==> (theta' has_vector_derivative theta'' t)(at t within s)) /\
  ke = (\u:real^(2,2)finite_sum. lift
           (&1 / &2 * (It + Mt * l * l + Mt * r * l * cos (fstcart u$1) + Ib + (Mb + Mt) * r * r)
                    * sndcart u$1 * sndcart u$1 +
            (Ib + (Mb + Mt) * r * r + Mt * r * l * cos (fstcart u$1)) * sndcart u$1 * sndcart u$2 +
            &1 / &2 * (Ib + (Mb + Mt) * r * r) * sndcart u$2 * sndcart u$2)) /\
  ue = (\u:real^2. lift(Mt * g * l * cos(u$1))) /\
  alpha = Ib + (Mb + Mt) * r * r /\ beta = Mt * r * l /\ gamma = It + Mt * l * l /\ mu = Mt * g * l /\
  M = vector [vector[alpha + gamma + beta * cos(drop(x t)); alpha + beta * cos(drop(x t))]:real^2;
              vector[alpha + beta * cos(drop(x t)); alpha]:real^2]:real^2^2 /\
  C = vector [vector[--(&1 / &2) * beta * sin(drop(x t)) * drop(x' t); &0]:real^2;
                vector[--beta * sin(drop(x t)) * drop(x' t); &0]:real^2]:real^2^2 /\
  G = vector [(--mu) * sin(drop(x t)); &0]:real^2/\
  f = (\t:real^1.(vector[lift(&0);lift(tau)]:real^1^2))/\
  rr =(\u:real^(2,1)finite_sum. (vector[lift(fstcart u$1);lift(fstcart u$2)]:real^1^2))/\
  lagrange_equations_autonomous s s0 s1 ke ue q f rr t
  ==> M ** (q'' t)+ C ** (q' t) + G = vector [&0; tau]`,
  INTRO_TAC "! * ; dropt s t s0 s1 q q' q'' xdif thetadif x'dif theta'dif ke ue alpha beta gamma mu M C G f rr lagrange" THEN
  CLAIM_TAC "vd_q"
  `!t. t IN s ==> (vector_derivative (q:real^1->real^2) (at t within s) =  ((q' (t:real^1)):real^2))` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN SIMP_TAC[has_vector_derivative] THEN ONCE_REWRITE_TAC[HAS_DERIVATIVE_COMPONENTWISE_WITHIN]
  THEN SIMP_TAC[FORALL_2;DIMINDEX_2] THEN HYP SIMP_TAC "q q'"[] THEN SIMP_TAC[VECTOR_2;LIFT_DROP;ETA_AX] THEN
  USE_THEN "xdif" MP_TAC THEN SIMP_TAC[VECTOR_MUL_COMPONENT;VECTOR_2] THEN SIMP_TAC[LIFT_CMUL;LIFT_DROP] THEN
  SIMP_TAC[has_vector_derivative] THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN USE_THEN "thetadif" MP_TAC THEN SIMP_TAC[has_vector_derivative] THEN ASM_SIMP_TAC[];ALL_TAC] THEN ABBREV_TAC `ke1_1 = (\u:real^(2,2)finite_sum. lift(&1 / &2 * (It + Mt * l * l + Mt * r * l * cos (fstcart u$1) + Ib + (Mb + Mt) * r * r)))` THEN
  ABBREV_TAC `ke1_1' = (\t. (\h:real^(2,2)finite_sum. vec 0 + vec 0 + (&1 / &2 * (Mt * r * l)) % lift (--sin (drop (x (t:real^1))) * (fstcart h$1)) + vec 0))` THEN
  CLAIM_TAC "ke1dif"
  `!t. t IN s ==> ((ke1_1:real^(2,2)finite_sum->real^1) has_derivative (ke1_1' t)) (at (qdq s q t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke1_1"  THEN EXPAND_TAC "ke1_1'"  THEN SIMP_TAC[LIFT_CMUL;LIFT_ADD;VECTOR_ADD_LDISTRIB] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[HAS_DERIVATIVE_CONST] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[HAS_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[HAS_DERIVATIVE_CONST] THEN SIMP_TAC[GSYM VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\u:real^(2,2)finite_sum. lift((fstcart u)$1)`;`lift o cos o drop`;
                `\h:real^(2,2)finite_sum. lift(fstcart h$1)`;`\h:real^1. --sin(drop(x (t':real^1))) % h`;
                `qdq s (q:real^1->real^2) t'`;`s1:real^(2,2)finite_sum->bool`]DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL[CONJ_TAC THENL
  [SIMP_TAC[has_vector_derivative;qdq_def] THEN SIMP_TAC[has_derivative_within;LIFT_SUB;FSTCART_SUB;VECTOR_SUB_COMPONENT;
  VECTOR_ARITH`x - (y + x - y) = vec 0 :real^1`] THEN SIMP_TAC[VECTOR_MUL_RZERO;LIM_CONST;linear;FSTCART_ADD;LIFT_ADD;
  VECTOR_ADD_COMPONENT;LIFT_CMUL;FSTCART_CMUL;VECTOR_MUL_COMPONENT];ALL_TAC] THEN
  SIMP_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN `fstcart (qdq s (q:real^1->real^2) t')$1 = drop(x t')` SUBST1_TAC THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;FSTCART_PASTECART] THEN HYP SIMP_TAC "q"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  SIMP_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS]; ALL_TAC] THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN
  ABBREV_TAC `ke1_2 = (\u:real^(2,2)finite_sum. lift (sndcart u$1 * sndcart u$1))` THEN
  ABBREV_TAC `ke1_2' = (\t.(\h:real^(2,2)finite_sum. lift (sndcart (qdq s (q:real^1->real^2) t)$1 * sndcart h$1) +
  lift (sndcart h$1 * sndcart (qdq s q t)$1)))` THEN
  CLAIM_TAC "ke1_2dif"
  `!t. t IN s ==> ((ke1_2:real^(2,2)finite_sum->real^1) has_derivative (ke1_2' t)) (at (qdq s q t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke1_2"  THEN EXPAND_TAC "ke1_2'" THEN
  MP_TAC (ISPECL [`(\u:real^(2,2)finite_sum. sndcart u$1)`;`(\h:real^(2,2)finite_sum. (sndcart h$1))`;`(\u:real^(2,2)finite_sum. lift (sndcart u$1))`;`(\h:real^(2,2)finite_sum. lift((sndcart h$1)))`;`(qdq s (q:real^1->real^2) t')`;`s1:real^(2,2)finite_sum->bool`] HAS_DERIVATIVE_MUL_WITHIN) THEN
  SIMP_TAC[o_DEF] THEN ANTS_TAC THENL
  [SIMP_TAC[DIMINDEX_2;ARITH;SNDCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT];ALL_TAC] THEN SIMP_TAC[GSYM LIFT_CMUL]; ALL_TAC] THEN
  ABBREV_TAC `ke1 = (\u:real^(2,2)finite_sum. drop(ke1_1 u) % (ke1_2 u)):real^(2,2)finite_sum->real^1` THEN
  ABBREV_TAC `ke1' = \t. ((\h:real^(2,2)finite_sum. drop(ke1_1 (qdq s q t)) % (ke1_2' t h) + drop(ke1_1' t h) % ke1_2 (qdq s (q:real^1->real^2) t)):real^(2,2)finite_sum->real^1)` THEN
  CLAIM_TAC "ke1dif"
  `!t. t IN s ==> ((ke1:real^(2,2)finite_sum->real^1) has_derivative ke1' t)(at (qdq s (q:real^1->real^2) t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke1" THEN EXPAND_TAC "ke1'" THEN
  MATCH_MP_TAC HAS_DERIVATIVE_MUL_WITHIN THEN SIMP_TAC[o_DEF;LIFT_DROP;ETA_AX] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  ABBREV_TAC `ke2_1 = (\u:real^(2,2)finite_sum. lift(Ib + (Mb + Mt) * r * r + Mt * r * l * cos (fstcart u$1)))` THEN
  ABBREV_TAC `ke2_1' = (\t.(\h:real^(2,2)finite_sum. vec 0 + vec 0 + (Mt * r * l) % lift (--sin (drop (x (t:real^1))) * (fstcart h$1))))`
  THEN CLAIM_TAC "ke2_1dif"
  `!t. t IN s ==> ((ke2_1:real^(2,2)finite_sum->real^1) has_derivative ke2_1' t) (at (qdq s q t) within s1)` THENL[
  REPEAT STRIP_TAC THEN  EXPAND_TAC "ke2_1" THEN EXPAND_TAC "ke2_1'" THEN SIMP_TAC[LIFT_ADD] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[HAS_DERIVATIVE_CONST] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[HAS_DERIVATIVE_CONST] THEN
  SIMP_TAC[GSYM VECTOR_MUL_ASSOC;LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\u:real^(2,2)finite_sum. lift((fstcart u)$1)`;`lift o cos o drop`;
                `\h:real^(2,2)finite_sum. lift(fstcart h$1)`;`\h:real^1. --sin(drop(x (t':real^1))) % h`;
                `qdq s (q:real^1->real^2) t'`;`s1:real^(2,2)finite_sum->bool`]DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL[CONJ_TAC THENL[SIMP_TAC[has_vector_derivative;qdq_def] THEN
  SIMP_TAC[has_derivative_within;LIFT_SUB;FSTCART_SUB;VECTOR_SUB_COMPONENT;VECTOR_ARITH`x - (y + x - y) = vec 0 :real^1`] THEN
  SIMP_TAC[VECTOR_MUL_RZERO;LIM_CONST;linear;FSTCART_ADD;LIFT_ADD;VECTOR_ADD_COMPONENT;LIFT_CMUL;FSTCART_CMUL;VECTOR_MUL_COMPONENT];ALL_TAC] THEN
  SIMP_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN `fstcart (qdq s (q:real^1->real^2) t')$1 = drop(x t')` SUBST1_TAC THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;FSTCART_PASTECART] THEN HYP SIMP_TAC "q"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  SIMP_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS;o_DEF;LIFT_DROP]; ALL_TAC] THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN
  ABBREV_TAC `ke2_2 = (\u:real^(2,2)finite_sum. lift (sndcart u$1 * sndcart u$2))` THEN
  ABBREV_TAC `ke2_2' = (\t.(\h:real^(2,2)finite_sum. lift (sndcart (qdq s (q:real^1->real^2) t)$1 * sndcart h$2) + lift (sndcart h$1 * sndcart (qdq s q t)$2)))` THEN
  CLAIM_TAC "ke1_2dif"
  `!t. t IN s ==> ((ke2_2:real^(2,2)finite_sum->real^1) has_derivative (ke2_2' t)) (at (qdq s q t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke2_2"  THEN EXPAND_TAC "ke2_2'" THEN
  MP_TAC (ISPECL [`(\u:real^(2,2)finite_sum. sndcart u$1)`;`(\h:real^(2,2)finite_sum. (sndcart h$1))`;
                  `(\u:real^(2,2)finite_sum. lift (sndcart u$2))`;`(\h:real^(2,2)finite_sum. lift((sndcart h$2)))`;
                  `(qdq s (q:real^1->real^2) t')`;`s1:real^(2,2)finite_sum->bool`] HAS_DERIVATIVE_MUL_WITHIN) THEN SIMP_TAC[o_DEF] THEN ANTS_TAC THENL
  [SIMP_TAC[DIMINDEX_2;ARITH;SNDCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT]; ALL_TAC] THEN SIMP_TAC[GSYM LIFT_CMUL]; ALL_TAC] THEN
  ABBREV_TAC `ke2 = (\u:real^(2,2)finite_sum. drop(ke2_1 u) % (ke2_2 u)):real^(2,2)finite_sum->real^1` THEN
  ABBREV_TAC `ke2' = \t.((\h:real^(2,2)finite_sum. drop(ke2_1 (qdq s q t)) % (ke2_2' t h) + drop(ke2_1' t h) % ke2_2 (qdq s (q:real^1->real^2) t)):real^(2,2)finite_sum->real^1)` THEN
  CLAIM_TAC "ke2dif"
  `!t. t IN s ==> ((ke2:real^(2,2)finite_sum->real^1) has_derivative ke2' t)(at (qdq s (q:real^1->real^2) t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke2" THEN EXPAND_TAC "ke2'" THEN MATCH_MP_TAC HAS_DERIVATIVE_MUL_WITHIN THEN SIMP_TAC[o_DEF;LIFT_DROP;ETA_AX] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  ABBREV_TAC `ke3_2 = (\u:real^(2,2)finite_sum. lift (sndcart u$2 * sndcart u$2))` THEN
  ABBREV_TAC `ke3_2' = \t.(\h:real^(2,2)finite_sum. lift (sndcart (qdq s (q:real^1->real^2) t)$2 * sndcart h$2) + lift (sndcart h$2 * sndcart (qdq s q t)$2))` THEN
  CLAIM_TAC "ke3_2dif"
  `!t. t IN s ==> ((ke3_2:real^(2,2)finite_sum->real^1) has_derivative ke3_2' t)(at (qdq s (q:real^1->real^2) t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke3_2" THEN EXPAND_TAC "ke3_2'" THEN
  MP_TAC (ISPECL [`(\u:real^(2,2)finite_sum. sndcart u$2)`;`(\h:real^(2,2)finite_sum. (sndcart h$2))`;
                  `(\u:real^(2,2)finite_sum. lift (sndcart u$2))`;`(\h:real^(2,2)finite_sum. lift((sndcart h$2)))`;
                  `(qdq s (q:real^1->real^2) t')`;`s1:real^(2,2)finite_sum->bool`] HAS_DERIVATIVE_MUL_WITHIN) THEN SIMP_TAC[o_DEF] THEN ANTS_TAC THENL
  [SIMP_TAC[DIMINDEX_2;ARITH;SNDCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT]; ALL_TAC] THEN SIMP_TAC[GSYM LIFT_CMUL]; ALL_TAC] THEN
  ABBREV_TAC `ke3 = (\u:real^(2,2)finite_sum. (&1 / &2 * (Ib + (Mb + Mt) * r * r)) % (ke3_2 u)):real^(2,2)finite_sum->real^1` THEN
  ABBREV_TAC `ke3' = \t.((\h:real^(2,2)finite_sum. (&1 / &2 * (Ib + (Mb + Mt) * r * r)) % (ke3_2' t h) + (&0) % ke3_2 (qdq s (q:real^1->real^2) t)):real^(2,2)finite_sum->real^1)` THEN
  CLAIM_TAC "ke3dif"
  `!t. t IN s ==> ((ke3:real^(2,2)finite_sum->real^1) has_derivative ke3' t)(at (qdq s (q:real^1->real^2) t) within s1)` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "ke3" THEN EXPAND_TAC "ke3'" THEN MATCH_MP_TAC HAS_DERIVATIVE_MUL_WITHIN THEN
  SIMP_TAC[o_DEF;LIFT_DROP;ETA_AX] THEN ASM_SIMP_TAC[LIFT_NUM;LIFT_EQ_CMUL;VECTOR_MUL_RZERO;HAS_DERIVATIVE_CONST];ALL_TAC] THEN
  ABBREV_TAC `ue' = \t.(\h:real^2. (Mt * g * l) % lift (--sin (drop (x (t:real^1))) * (h$1)))` THEN
  ABBREV_TAC `s2 = {u:real^2 | ?y. y IN mspace(fspace s) /\ u IN IMAGE y s}` THEN
  CLAIM_TAC "uedif"
  `!t. t IN s ==> ((ue:real^2->real^1) has_derivative ue' t)(at (q (t:real^1)) within s2)` THENL[
  REPEAT STRIP_TAC THEN HYP SIMP_TAC "ue"[] THEN EXPAND_TAC "ue'" THEN SIMP_TAC[LIFT_CMUL;GSYM VECTOR_MUL_ASSOC;LIFT_CMUL] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\u:real^2. lift(u$1)`;`lift o cos o drop`;`\h:real^2. lift(h$1)`;
                `\h:real^1. --sin(drop(x (t':real^1))) % h`;`(q:real^1->real^2) t'`;`s2:real^2->bool`]DIFF_CHAIN_WITHIN) THEN ANTS_TAC THENL[
  CONJ_TAC THENL
  [SIMP_TAC[has_vector_derivative;qt_def] THEN SIMP_TAC[has_derivative_within;LIFT_SUB;FSTCART_SUB;VECTOR_SUB_COMPONENT; VECTOR_ARITH`x - (y + x - y) = vec 0 :real^1`] THEN SIMP_TAC[VECTOR_MUL_RZERO;LIM_CONST;linear;FSTCART_ADD;LIFT_ADD;VECTOR_ADD_COMPONENT;LIFT_CMUL;FSTCART_CMUL;VECTOR_MUL_COMPONENT];ALL_TAC] THEN
  SIMP_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN `((q:real^1->real^2) t')$1 = drop(x t')` SUBST1_TAC THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;FSTCART_PASTECART] THEN HYP SIMP_TAC "q"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  SIMP_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS;o_DEF;LIFT_DROP]; ALL_TAC] THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN
  ABBREV_TAC `ke_ = (\u:real^(2,2)finite_sum. (((ke1 u):real^1)+ ke2 u+ ke3 u)) ` THEN
  ABBREV_TAC `ke_' =(\t:real^1. (\h:real^(2,2)finite_sum. ((ke1' t h) +(ke2' t h) +(ke3' t h))):real^(2,2)finite_sum->real^1)` THEN
  CLAIM_TAC "ke_dif"
  `!t. t IN s ==> ((ke_:real^(2,2)finite_sum->real^1) has_derivative ke_' t)(at (qdq (s:real^1->bool) (q:real^1->real^2) t) within s1)` THENL[
  REPEAT STRIP_TAC THEN EXPAND_TAC "ke_" THEN EXPAND_TAC "ke_'" THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[o_DEF;LIFT_DROP;ETA_AX] THEN
  CONJ_TAC THENL[ASM_SIMP_TAC[];ALL_TAC] THEN MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN SIMP_TAC[o_DEF;LIFT_DROP;ETA_AX] THEN
  CONJ_TAC THENL[ASM_SIMP_TAC[];ALL_TAC] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CLAIM_TAC "ke_sub_ue_dif"
  `!t. t IN s ==> ((\u:real^(2,2)finite_sum. ((ke_ u - ue (fstcart u)):real^1)) has_derivative
              ((\h:real^(2,2)finite_sum. (ke_' t h - ue' t (fstcart h))):real^(2,2)finite_sum->real^1)) (at (qdq s (q:real^1->real^2) t) within s1)` THENL[
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL[SIMP_TAC[ETA_AX] THEN ASM_SIMP_TAC[];ALL_TAC] THEN HYP SIMP_TAC "ue"[] THEN
  EXPAND_TAC "ue'" THEN SIMP_TAC[GSYM VECTOR_MUL_ASSOC;LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\u:real^(2,2)finite_sum. lift((fstcart u)$1)`;`lift o cos o drop`;`\h:real^(2,2)finite_sum. lift(fstcart h$1)`;
                `\h:real^1. --sin(drop(x (t':real^1))) % h`;`qdq s (q:real^1->real^2) t'`;`s1:real^(2,2)finite_sum->bool`]DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL[CONJ_TAC THENL[SIMP_TAC[has_vector_derivative;qdq_def] THEN SIMP_TAC[has_derivative_within;LIFT_SUB;FSTCART_SUB;VECTOR_SUB_COMPONENT;
  VECTOR_ARITH`x - (y + x - y) = vec 0 :real^1`] THEN SIMP_TAC[VECTOR_MUL_RZERO;LIM_CONST;linear;FSTCART_ADD;LIFT_ADD;VECTOR_ADD_COMPONENT;LIFT_CMUL;
  FSTCART_CMUL;VECTOR_MUL_COMPONENT];ALL_TAC] THEN SIMP_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
  SUBGOAL_THEN `fstcart (qdq s (q:real^1->real^2) t')$1 = drop(x t')` SUBST1_TAC THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;FSTCART_PASTECART] THEN HYP SIMP_TAC "q"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  SIMP_TAC[GSYM HAS_REAL_FRECHET_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS;o_DEF;LIFT_DROP]; ALL_TAC] THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN
  CLAIM_TAC "ke_ke_eq"
  `ke:real^(2,2)finite_sum->real^1 = ke_:real^(2,2)finite_sum->real^1` THENL
  [HYP SIMP_TAC "ke"[] THEN EXPAND_TAC "ke_" THEN EXPAND_TAC "ke1" THEN EXPAND_TAC "ke2" THEN EXPAND_TAC "ke3" THEN EXPAND_TAC "ke1_1" THEN
  EXPAND_TAC "ke1_2" THEN EXPAND_TAC "ke2_1" THEN EXPAND_TAC "ke2_2" THEN EXPAND_TAC "ke3_2" THEN SIMP_TAC[LIFT_DROP] THEN SIMP_TAC[GSYM LIFT_CMUL;LIFT_ADD] THEN
  SIMP_TAC[GSYM LIFT_CMUL;GSYM LIFT_ADD;REAL_MUL_ASSOC] ;ALL_TAC] THEN SIMP_TAC[CART_EQ;DIMINDEX_2;FORALL_2] THEN
  CLAIM_TAC "fretlag"
  `!t. t IN s ==>
  frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) (ue:real^2->real^1)) (at (qdq (s:real^1->bool) (q:real^1->real^2) t) within (s1:real^(2,2)finite_sum->bool)) = (\t:real^1.(\h:real^(2,2)finite_sum. ke_' t h - ue' t (fstcart h)):real^(2,2)finite_sum->real^1) t` THENL [
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
  MAP_EVERY EXISTS_TAC[`(lagrange_function_autonomous ke ue):real^(2,2)finite_sum->real^1`;`qdq s (q:real^1->real^2) t'`;`s1:real^(2,2)finite_sum->bool`] THEN SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN REWRITE_TAC[lagrange_function_autonomous] THEN CONJ_TAC THENL [ASM_MESON_TAC[differentiable];ALL_TAC] THEN CONJ_TAC THENL [HYP SIMP_TAC "ke_ke_eq"[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN INTRO_TAC "![k] [e]; k1 kQQ1 e" THEN EXISTS_TAC `e / &2` THEN
  HYP SIMP_TAC "e" [REAL_ARITH`&0 < e ==> &0 < abs(e / &2) /\ abs(e / &2) < e`] THEN SIMP_TAC[qdq_def;fpt;fun_map_2] THEN EXPAND_TAC "s1" THEN EXPAND_TAC "s" THEN
  SIMP_TAC[IN_ELIM_THM;IN_IMAGE;FSPACE;COMPACT_INTERVAL] THEN EXISTS_TAC `\t:real^1. if t IN interval[t0,t1] then
  pastecart (q t' :real^2) (higher_vector_derivative 1 q s t' :real^2) + e / &2 % basis k else vec 0` THEN SIMP_TAC[continuous_on] THEN SIMP_TAC[GSYM continuous_on]
  THEN CONJ_TAC THENL[MATCH_MP_TAC CONTINUOUS_ON_ADD THEN  SIMP_TAC[CONTINUOUS_ON_CONST;CONTINUOUS_ON_THREE_FPT] ;ALL_TAC] THEN
  EXISTS_TAC `t':real^1` THEN HYP SIMP_TAC "s"[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CLAIM_TAC "fq1"
  `(!t. t IN s ==> fstcart(qdq (s:real^1->bool) (q:real^1->real^2) t)$1 = drop (x t))` THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;FSTCART_PASTECART] THEN HYP SIMP_TAC "q"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  CLAIM_TAC "sq1"
  `(!t. t IN s ==> sndcart(qdq (s:real^1->bool) (q:real^1->real^2) t)$1 = drop (x' t))` THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;SNDCART_PASTECART] THEN SIMP_TAC[num_CONV `1`; higher_vector_derivative;vector_fun_derivative;GSYM vector_derivative] THEN SIMP_TAC[ARITH_RULE`SUC 0 = 1`] THEN HYP SIMP_TAC "vd_q q'"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  CLAIM_TAC "sq2"
  `(!t. t IN s ==> sndcart (qdq (s:real^1->bool) (q:real^1->real^2) t)$2 = drop (theta' t))` THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;SNDCART_PASTECART] THEN SIMP_TAC[num_CONV `1`; higher_vector_derivative;vector_fun_derivative;GSYM vector_derivative] THEN
  SIMP_TAC[ARITH_RULE`SUC 0 = 1`] THEN HYP SIMP_TAC "vd_q q'"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  CLAIM_TAC "fcu_hd"
  `((\u:real^(2,1)finite_sum. lift(fstcart u$2)) has_derivative (\u:real^(2,1)finite_sum. lift(fstcart u$2))) (at (qt (q:real^1->real^2)  (t:real^1)) within (s0:real^(2,1)finite_sum->bool))` THENL[SIMP_TAC[DIMINDEX_2;ARITH;FSTCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT] ;ALL_TAC] THEN
  CLAIM_TAC "fd_u2"
  `frechet_derivative (\u:real^(2,1)finite_sum. lift (fstcart u$2)) (at (qt (q:real^1->real^2) (t:real^1)) within (s0:real^(2,1)finite_sum->bool)) = (\u:real^(2,1)finite_sum. lift(fstcart u$2))` THENL
  [MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
  MAP_EVERY EXISTS_TAC[`(\u:real^(2,1)finite_sum. lift (fstcart u$2))`;`(qt (q:real^1->real^2) (t:real^1))`;`s0:real^(2,1)finite_sum->bool`] THEN
  SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THENL [ASM_MESON_TAC[differentiable];ALL_TAC] THEN
  HYP SIMP_TAC "fcu_hd"[] THEN INTRO_TAC "![k] [e]; k1 kQQ1 e" THEN EXISTS_TAC `e / &2` THEN
  HYP SIMP_TAC "e" [REAL_ARITH`&0 < e ==> &0 < abs(e / &2) /\ abs(e / &2) < e`] THEN SIMP_TAC[qt_def;fpt;fun_map_2] THEN
  EXPAND_TAC "s0" THEN EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM;IN_IMAGE;FSPACE;COMPACT_INTERVAL] THEN
  EXISTS_TAC `\t':real^1. if t' IN interval[t0,t1] then
  pastecart (q t:real^2) (t:real^1) + e / &2 % basis k else vec 0` THEN SIMP_TAC[continuous_on] THEN SIMP_TAC[GSYM continuous_on]
  THEN CONJ_TAC THENL[MATCH_MP_TAC CONTINUOUS_ON_ADD THEN  SIMP_TAC[CONTINUOUS_ON_CONST;CONTINUOUS_ON_THREE_FPT] ;ALL_TAC] THEN
  EXISTS_TAC `t:real^1` THEN HYP SIMP_TAC "s"[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CONJ_TAC THENL[USE_THEN "lagrange" MP_TAC THEN REWRITE_TAC[lagrange_equations_autonomous] THEN DISCH_THEN(MP_TAC o SPEC`1`) THEN SIMP_TAC[IN_NUMSEG;DIMINDEX_2;ARITH] THEN HYP SIMP_TAC "M C G q' q'' alpha beta gamma mu"[] THEN REWRITE_TAC[VECTOR_ADD_COMPONENT;VECTOR_2] THEN
  SIMP_TAC[DIMINDEX_GE_1;LE_REFL;MATRIX_VECTOR_MUL_COMPONENT;DOT_2;VECTOR_2]
  THEN SIMP_TAC[jacobian;CART_EQ;DIMINDEX_1;FORALL_1;VECTOR_SUB_COMPONENT;LIFT_COMPONENT;TRANSP_COMPONENT] THEN
  CLAIM_TAC "matrix_fretlag"
  `(matrix(frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) ue) (at (qdq s (q:real^1->real^2) t) within s1)))$1$1 =
  ((--((&1)/(&2)))*(Mt * r * l * (sin (drop (x (t:real^1)))) * (sndcart(qdq s (q:real^1->real^2) t)$1) * (sndcart(qdq s (q:real^1->real^2) t)$1))) -
  (Mt * r * l * (sin (drop (x (t:real^1)))) * (sndcart(qdq s (q:real^1->real^2) t)$1) * (sndcart(qdq s (q:real^1->real^2) t)$2)) + Mt * g * l * (sin (drop (x (t:real^1))))` THENL [
  HYP SIMP_TAC "fretlag t"[] THEN EXPAND_TAC "ke_'" THEN EXPAND_TAC "ue'" THEN EXPAND_TAC "ke1'" THEN EXPAND_TAC "ke2'" THEN EXPAND_TAC "ke3'" THEN
  EXPAND_TAC "ke1_1" THEN EXPAND_TAC "ke1_2'" THEN EXPAND_TAC "ke1_1'" THEN EXPAND_TAC "ke1_2" THEN EXPAND_TAC "ke2_1" THEN EXPAND_TAC "ke2_2'"
  THEN EXPAND_TAC "ke2_1'" THEN EXPAND_TAC "ke2_2" THEN EXPAND_TAC "ke3_2'" THEN EXPAND_TAC "ke3_2" THEN SIMP_TAC[MATRIX_COMPONENT;DIMINDEX_GE_1;LE_REFL] THEN
  SIMP_TAC[VECTOR_MUL_LZERO;VECTOR_ADD_LID;FSTCART_COMPONENT;BASIS_COMPONENT;DIMINDEX_GE_1;LE_REFL;SNDCART_COMPONENT;DIMINDEX_2;ARITH_RULE `1<=2`;ARITH;
  DIMINDEX_FINITE_SUM;LIFT_NUM;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;VECTOR_MUL_RZERO;VECTOR_ADD_COMPONENT;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;
  VECTOR_ADD_RID;VEC_COMPONENT;LIFT_COMPONENT;REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;DROP_CMUL;LIFT_DROP] THEN REAL_ARITH_TAC;ALL_TAC] THEN
  CLAIM_TAC "vd_tmfl"
  `vector_derivative (\t. transp(matrix(frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) (ue:real^2->real^1))
  (at (qdq (s:real^1->bool) (q:real^1->real^2) t) within (s1:real^(2,2)finite_sum->bool))))$3) (at t within s) =
  (lift((lift It +lift (Mt * l * l) +lift ((Mt * r * l) * cos (drop (x t))) +lift Ib + lift ((Mb + Mt) * r * r)) dot x'' t) +
  lift((vec 0 +vec 0 +(Mt * r * l) % drop (x' t) % lift (--sin (drop (x t))) + vec 0 + vec 0) dot x' t)) +
  lift((lift Ib +lift ((Mb + Mt) * r * r) +lift ((Mt * r * l) * cos (drop (x t)))) dot theta'' t) +
  lift((vec 0 +vec 0 +(Mt * r * l) % drop (x' t) % lift (--sin (drop (x t)))) dot theta' t)` THENL[
  EXPAND_TAC "s" THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN HYP SIMP_TAC "dropt s t"[] THEN
  SIMP_TAC[HAS_VECTOR_REAL_DERIVATIVE_WITHIN;o_DEF;drop;TRANSP_COMPONENT;MATRIX_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_2;ARITH]
  THEN SIMP_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN;o_DEF;LIFT_DROP;LIFT_COMPONENT] THEN SIMP_TAC[GSYM drop;LIFT_DROP;GSYM IMAGE_o;o_DEF;IMAGE_ID] THEN HYP SIMP_TAC "t fretlag" [has_vector_derivative;HAS_DERIVATIVE_WITHIN] THEN SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN;GSYM has_vector_derivative] THEN EXPAND_TAC "ke_'" THEN
  EXPAND_TAC "ue'" THEN EXPAND_TAC "ke1'" THEN EXPAND_TAC "ke2'" THEN EXPAND_TAC "ke3'" THEN EXPAND_TAC "ke1_1" THEN EXPAND_TAC "ke1_2'" THEN
  EXPAND_TAC "ke1_1'" THEN EXPAND_TAC "ke1_2" THEN EXPAND_TAC "ke2_1" THEN EXPAND_TAC "ke2_2'" THEN EXPAND_TAC "ke2_1'" THEN EXPAND_TAC "ke2_2"
  THEN EXPAND_TAC "ke3_2'" THEN EXPAND_TAC "ke3_2" THEN SIMP_TAC[LIFT_DROP] THEN SIMP_TAC[has_vector_derivative] THEN SIMP_TAC[HAS_DERIVATIVE_WITHIN_ALT]
  THEN HYP SIMP_TAC "t fq1 sq1 sq2"[] THEN SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN_ALT] THEN SIMP_TAC[GSYM has_vector_derivative] THEN
  SIMP_TAC[FSTCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN SIMP_TAC[SNDCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[BASIS_COMPONENT;DIMINDEX_GE_1;DIMINDEX_FINITE_SUM;DIMINDEX_1;DIMINDEX_2;LE_REFL;ARITH] THEN SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
  CLAIM_TAC "tr_eq"
  `(\t:real^1.(((&1 / &2 *(It +Mt * l * l +Mt * r * l * cos (drop (x t)) +Ib +(Mb + Mt) * r * r)) % (lift (drop (x' t)) + lift (drop (x' t))) +
                drop (vec 0 + vec 0 + (&1 / &2 * Mt * r * l) % lift (&0) + vec 0) % lift (drop (x' t) * drop (x' t))) +
                ((Ib + (Mb + Mt) * r * r + Mt * r * l * cos (drop (x t))) % (lift (&0) + lift (drop (theta' t))) +
                drop (vec 0 + vec 0 + (Mt * r * l) % lift (&0)) % lift (drop (x' t) * drop (theta' t))) +
                (&1 / &2 * (Ib + (Mb + Mt) * r * r)) % (lift (&0) + lift (&0)) +
                &0 % lift (drop (theta' t) * drop (theta' t))) -(Mt * g * l) % lift (&0)) =
                (\t:real^1. lift((lift(It +Mt * l * l + (Mt * r * l) * cos (drop (x (t:real^1))) +Ib +(Mb + Mt) * r * r) dot lift(drop (x' (t:real^1)))) +
                lift(Ib + (Mb + Mt) * r * r + (Mt * r * l) * cos (drop (x (t:real^1)))) dot lift(drop(theta' (t:real^1)))))` THENL
  [SIMP_TAC[DOT_1;LIFT_COMPONENT] THEN SIMP_TAC[FUN_EQ_THM] THEN INTRO_TAC "![t']" THEN SIMP_TAC[LIFT_NUM;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;VECTOR_MUL_RZERO; VECTOR_ADD_COMPONENT;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;
  VECTOR_ADD_RID;VEC_COMPONENT;LIFT_COMPONENT;REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;DROP_CMUL;LIFT_DROP] THEN
  SIMP_TAC[DROP_VEC;VECTOR_MUL_LZERO;VECTOR_ADD_LID;VECTOR_ADD_RID;VECTOR_SUB_RZERO;LIFT_ADD;LIFT_CMUL;LIFT_DROP] THEN VECTOR_ARITH_TAC;ALL_TAC] THEN HYP SIMP_TAC "tr_eq"[] THEN SIMP_TAC[LIFT_ADD] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[LIFT_DROP] THEN  CONJ_TAC THENL
  [MP_TAC(ISPECL[`\t:real^1.(lift It +lift (Mt * l * l) +lift ((Mt * r * l) * cos (drop ((x t):real^1))) +lift Ib +lift ((Mb + Mt) * r * r))`;
                 `\t:real^1.(x' t):real^1`;
                 `\t:real^1. ((vec 0 +vec 0 +(Mt * r * l) % (drop((x' t):real^1) % lift(--sin (drop ((x t):real^1)))) +vec 0 +vec 0))`;
                 `\t:real^1.(x'' t):real^1`;`s:real^1->bool`;`t:real^1`]HAS_VECTOR_DERIVATIVE_WITHIN_LIFT_DOT2) THEN SIMP_TAC[ETA_AX] THEN
  ANTS_TAC THENL[CONJ_TAC THENL [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  CONJ_TAC THENL [SIMP_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\t:real^1.lift(drop((x t):real^1))`;`lift o cos o drop`;`x' (t:real^1):real^1`;
                `lift(--sin (drop ((x (t:real^1)):real^1)))`;`s:real^1->bool`;`t:real^1`]VECTOR_DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL[CONJ_TAC THENL[SIMP_TAC[LIFT_DROP;ETA_AX] THEN HYP SIMP_TAC "t xdif"[];ALL_TAC] THEN SIMP_TAC[] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN SIMP_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS];ALL_TAC]
  THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST];ALL_TAC]
  THEN HYP SIMP_TAC "x'dif t"[];ALL_TAC] THEN SIMP_TAC[ETA_AX];ALL_TAC] THEN
  MP_TAC(ISPECL[`\t:real^1.(lift Ib +lift ((Mb + Mt) * r * r) +lift ((Mt * r * l) * cos (drop ((x t):real^1))))`;
                `\t:real^1.(theta' t):real^1`;
                `\t:real^1.(vec 0 + vec 0 + (Mt * r * l) % drop ((x' t):real^1) % lift (--sin (drop ((x t):real^1))))`;
                `\t:real^1.(theta'' t):real^1`;`s:real^1->bool`;`t:real^1`]HAS_VECTOR_DERIVATIVE_WITHIN_LIFT_DOT2) THEN SIMP_TAC[ETA_AX] THEN
  ANTS_TAC THENL[CONJ_TAC THENL [MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN SIMP_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\t:real^1.lift(drop((x t):real^1))`;`lift o cos o drop`;`x' (t:real^1):real^1`;
                `lift(--sin (drop ((x (t:real^1)):real^1)))`;`s:real^1->bool`;`t:real^1`
                    ]VECTOR_DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL[CONJ_TAC THENL[SIMP_TAC[LIFT_DROP;ETA_AX] THEN HYP SIMP_TAC "t xdif"[];ALL_TAC] THEN
  SIMP_TAC[] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN SIMP_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS];ALL_TAC]
  THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN HYP SIMP_TAC "theta'dif t"[];ALL_TAC] THEN SIMP_TAC[ETA_AX];ALL_TAC]
  THEN HYP SIMP_TAC "vd_tmfl"[] THEN SIMP_TAC[VECTOR_ADD_LID;VECTOR_ADD_RID] THEN SIMP_TAC[DOT_1;VECTOR_ADD_COMPONENT;LIFT_COMPONENT] THEN SIMP_TAC[GSYM LIFT_CMUL;LIFT_COMPONENT] THEN HYP SIMP_TAC "matrix_fretlag"[] THEN SIMP_TAC[VECTOR_2] THEN
  SUBGOAL_THEN `sndcart(qdq (s:real^1->bool) (q:real^1->real^2) t)$1 = drop (x' t)` SUBST1_TAC THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;SNDCART_PASTECART] THEN SIMP_TAC[num_CONV `1`; higher_vector_derivative;vector_fun_derivative;GSYM vector_derivative] THEN
  SIMP_TAC[ARITH_RULE`SUC 0 = 1`] THEN  HYP SIMP_TAC "vd_q t q'"[] THEN SIMP_TAC[VECTOR_2];ALL_TAC] THEN
  SUBGOAL_THEN `sndcart (qdq (s:real^1->bool) (q:real^1->real^2) t)$2 = drop (theta' t)` SUBST1_TAC THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;SNDCART_PASTECART] THEN SIMP_TAC[num_CONV `1`; higher_vector_derivative;vector_fun_derivative;GSYM vector_derivative] THEN
  SIMP_TAC[ARITH_RULE`SUC 0 = 1`] THEN  HYP SIMP_TAC "vd_q t q'"[] THEN SIMP_TAC[VECTOR_2];ALL_TAC] THEN
  SIMP_TAC[REAL_MUL_LZERO;REAL_ADD_RID] THEN SIMP_TAC[GSYM drop] THEN HYP SIMP_TAC "f rr"[] THEN SIMP_TAC[generalized_forces] THEN
  SIMP_TAC[LAMBDA_BETA;LE_REFL;DIMINDEX_GE_1] THEN SIMP_TAC[DIMINDEX_2;SUM_2] THEN SIMP_TAC[VECTOR_2;LIFT_NUM;DOT_LZERO;REAL_ADD_LID] THEN
  HYP SIMP_TAC "fd_u2"[] THEN SIMP_TAC[FSTCART_COMPONENT;LE_REFL;DIMINDEX_2;ARITH] THEN SIMP_TAC[BASIS_COMPONENT;LE_REFL;DIMINDEX_FINITE_SUM;DIMINDEX_1;
  DIMINDEX_2;ARITH] THEN SIMP_TAC[LIFT_NUM;DOT_LZERO;DOT_RZERO] THEN REAL_ARITH_TAC ;ALL_TAC] THEN
  USE_THEN "lagrange" MP_TAC THEN REWRITE_TAC[lagrange_equations_autonomous] THEN DISCH_THEN(MP_TAC o SPEC`2`) THEN SIMP_TAC[IN_NUMSEG;DIMINDEX_2;ARITH] THEN HYP SIMP_TAC "M C G q' q'' alpha beta gamma mu"[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT;VECTOR_2] THEN SIMP_TAC[DIMINDEX_2;ARITH;MATRIX_VECTOR_MUL_COMPONENT;DOT_2;VECTOR_2;REAL_ADD_RID;REAL_MUL_LZERO] THEN
  SIMP_TAC[jacobian;CART_EQ;DIMINDEX_1;FORALL_1;VECTOR_SUB_COMPONENT;LIFT_COMPONENT;TRANSP_COMPONENT] THEN
  CLAIM_TAC "matrix_fretlag"
  `(matrix(frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) ue) (at (qdq s (q:real^1->real^2) t) within s1)))$1$2 = &0`THENL
  [HYP SIMP_TAC "fretlag t"[] THEN EXPAND_TAC "ke_'" THEN EXPAND_TAC "ue'" THEN EXPAND_TAC "ke1'" THEN EXPAND_TAC "ke2'" THEN EXPAND_TAC "ke3'" THEN
  EXPAND_TAC "ke1_1" THEN EXPAND_TAC "ke1_2'" THEN EXPAND_TAC "ke1_1'" THEN EXPAND_TAC "ke1_2" THEN EXPAND_TAC "ke2_1"
  THEN EXPAND_TAC "ke2_2'" THEN EXPAND_TAC "ke2_1'" THEN EXPAND_TAC "ke2_2" THEN EXPAND_TAC "ke3_2'" THEN EXPAND_TAC "ke3_2" THEN
  SIMP_TAC[MATRIX_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_2;ARITH] THEN
  SIMP_TAC[VECTOR_MUL_LZERO;VECTOR_ADD_LID;FSTCART_COMPONENT;BASIS_COMPONENT;DIMINDEX_GE_1;LE_REFL;SNDCART_COMPONENT;DIMINDEX_2;ARITH_RULE `1<=2`;ARITH;
  DIMINDEX_FINITE_SUM;LIFT_NUM;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;VECTOR_MUL_RZERO;VECTOR_ADD_COMPONENT;
  VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;VECTOR_ADD_RID;VEC_COMPONENT;LIFT_COMPONENT;REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;DROP_CMUL;
  LIFT_DROP;DROP_VEC] THEN REAL_ARITH_TAC;ALL_TAC] THEN
  CLAIM_TAC "vd_tmfl"
  `vector_derivative (\t. transp(matrix
  (frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) (ue:real^2->real^1))
  (at (qdq (s:real^1->bool) (q:real^1->real^2) t) within (s1:real^(2,2)finite_sum->bool))))$4) (at t within s) =
  (lift((lift Ib +lift ((Mb + Mt) * r * r) +lift (Mt * r * l * cos (drop (x (t:real^1))))) dot x'' t) +
  lift((vec 0 + vec 0 + (Mt * r * l) % drop (x' t) % lift (--sin (drop (x t)))) dot x' t)) + lift((lift Ib + lift((Mb + Mt) * r * r)) dot theta'' t)` THENL[
  EXPAND_TAC "s" THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN HYP SIMP_TAC "dropt s t"[] THEN
  SIMP_TAC[HAS_VECTOR_REAL_DERIVATIVE_WITHIN;o_DEF;drop;TRANSP_COMPONENT;MATRIX_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_2;ARITH]
  THEN SIMP_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN;o_DEF;LIFT_DROP;LIFT_COMPONENT] THEN SIMP_TAC[GSYM drop;LIFT_DROP;GSYM IMAGE_o;o_DEF;IMAGE_ID] THEN HYP SIMP_TAC "t fretlag" [has_vector_derivative;HAS_DERIVATIVE_WITHIN] THEN SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN;GSYM has_vector_derivative] THEN EXPAND_TAC "ke_'" THEN
  EXPAND_TAC "ue'" THEN EXPAND_TAC "ke1'" THEN EXPAND_TAC "ke2'" THEN EXPAND_TAC "ke3'" THEN
  EXPAND_TAC "ke1_1" THEN EXPAND_TAC "ke1_2'" THEN EXPAND_TAC "ke1_1'" THEN EXPAND_TAC "ke1_2" THEN EXPAND_TAC "ke2_1"
  THEN EXPAND_TAC "ke2_2'" THEN EXPAND_TAC "ke2_1'" THEN EXPAND_TAC "ke2_2" THEN EXPAND_TAC "ke3_2'" THEN EXPAND_TAC "ke3_2"
  THEN SIMP_TAC[LIFT_DROP] THEN SIMP_TAC[has_vector_derivative] THEN SIMP_TAC[HAS_DERIVATIVE_WITHIN_ALT] THEN HYP SIMP_TAC "t fq1 sq1 sq2"[] THEN
  SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN_ALT] THEN SIMP_TAC[GSYM has_vector_derivative] THEN SIMP_TAC[FSTCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[SNDCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[BASIS_COMPONENT;DIMINDEX_GE_1;DIMINDEX_FINITE_SUM;DIMINDEX_1;DIMINDEX_2;LE_REFL;ARITH] THEN
  SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
  CLAIM_TAC "tr_eq"
  `(\t:real^1. (((&1 / &2 *(It +Mt * l * l +Mt * r * l * cos (drop (x t)) +Ib +(Mb + Mt) * r * r)) % (lift (&0) + lift (&0)) +
                  drop (vec 0 + vec 0 + (&1 / &2 * Mt * r * l) % lift (&0) + vec 0) % lift (drop (x' t) * drop (x' t))) +
                 ((Ib + (Mb + Mt) * r * r + Mt * r * l * cos (drop (x t))) % (lift (drop (x' t)) + lift (&0)) +
                 drop (vec 0 + vec 0 + (Mt * r * l) % lift (&0)) % lift (drop (x' t) * drop (theta' t))) +
                 (&1 / &2 * (Ib + (Mb + Mt) * r * r)) % (lift (drop (theta' t)) + lift (drop (theta' t))) +
                 &0 % lift (drop (theta' t) * drop (theta' t))) - (Mt * g * l) % lift (&0)) =
  (\t:real^1.lift((lift(Ib + (Mb + Mt) * r * r + Mt * r * l * cos (drop (x (t:real^1))))) dot lift(drop (x' (t:real^1)))) +
               lift(lift(Ib + (Mb + Mt) * r *r) dot lift(drop(theta' (t:real^1)))))` THENL[
  SIMP_TAC[DOT_1;LIFT_COMPONENT] THEN SIMP_TAC[FUN_EQ_THM] THEN INTRO_TAC "![t']" THEN
  SIMP_TAC[LIFT_NUM;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;VECTOR_MUL_RZERO;
  VECTOR_ADD_COMPONENT;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;VECTOR_ADD_RID;VEC_COMPONENT;LIFT_COMPONENT;REAL_ADD_LID;REAL_ADD_RID;
  REAL_MUL_LZERO;REAL_MUL_RZERO;DROP_CMUL;LIFT_DROP] THEN SIMP_TAC[DROP_VEC;VECTOR_MUL_LZERO;VECTOR_ADD_LID;VECTOR_ADD_RID;VECTOR_SUB_RZERO;LIFT_ADD;LIFT_CMUL;LIFT_DROP]
  THEN VECTOR_ARITH_TAC;ALL_TAC] THEN HYP SIMP_TAC "tr_eq"[] THEN SIMP_TAC[LIFT_ADD] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[LIFT_DROP] THEN CONJ_TAC THENL[
  MP_TAC(ISPECL[`\t:real^1.lift(Ib + (Mb + Mt) * r * r + Mt * r * l * cos (drop (x (t:real^1))))`;
                `\t:real^1.(x' t):real^1`;
                `\t:real^1. (vec 0 + vec 0 + (Mt * r * l) % drop ((x' t):real^1) % lift (--sin (drop ((x t):real^1))))`;
                `\t:real^1.(x'' t):real^1`;`s:real^1->bool`;`t:real^1`]HAS_VECTOR_DERIVATIVE_WITHIN_LIFT_DOT2) THEN
  SIMP_TAC[ETA_AX] THEN ANTS_TAC THENL[CONJ_TAC THENL[
  SIMP_TAC[LIFT_ADD] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_ADD THEN
  SIMP_TAC[HAS_VECTOR_DERIVATIVE_CONST] THEN SIMP_TAC[LIFT_CMUL;GSYM VECTOR_MUL_ASSOC] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN
  MP_TAC(ISPECL[`\t:real^1.lift(drop((x t):real^1))`;`lift o cos o drop`;`x' (t:real^1):real^1`;
                `lift(--sin (drop ((x (t:real^1)):real^1)))`;`s:real^1->bool`;`t:real^1`]VECTOR_DIFF_CHAIN_WITHIN) THEN
  ANTS_TAC THENL[CONJ_TAC THENL[SIMP_TAC[LIFT_DROP;ETA_AX] THEN HYP SIMP_TAC "t xdif"[];ALL_TAC] THEN
  SIMP_TAC[] THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN SIMP_TAC[GSYM HAS_REAL_VECTOR_DERIVATIVE_AT;HAS_REAL_DERIVATIVE_COS];ALL_TAC] THEN SIMP_TAC[o_DEF;LIFT_DROP];ALL_TAC] THEN HYP SIMP_TAC "x'dif t"[];ALL_TAC] THEN SIMP_TAC[LIFT_ADD];ALL_TAC] THEN
  MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_LIFT_DOT_RIGHT THEN HYP SIMP_TAC "theta'dif t"[];ALL_TAC] THEN HYP SIMP_TAC "vd_tmfl matrix_fretlag"[] THEN
  SIMP_TAC[VECTOR_ADD_LID;VECTOR_ADD_RID] THEN SIMP_TAC[DOT_1;VECTOR_ADD_COMPONENT;LIFT_COMPONENT] THEN SIMP_TAC[GSYM LIFT_CMUL;LIFT_COMPONENT] THEN
  SIMP_TAC[GSYM drop;REAL_SUB_RZERO] THEN HYP SIMP_TAC "f rr"[] THEN SIMP_TAC[generalized_forces] THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_2;ARITH] THEN
  SIMP_TAC[SUM_2;VECTOR_2;LIFT_NUM;DOT_LZERO;REAL_ADD_LID] THEN HYP SIMP_TAC "fd_u2"[] THEN SIMP_TAC[FSTCART_COMPONENT;LE_REFL;DIMINDEX_2;ARITH] THEN
  SIMP_TAC[BASIS_COMPONENT;LE_REFL;DIMINDEX_FINITE_SUM;DIMINDEX_1;DIMINDEX_2;ARITH] THEN SIMP_TAC[DOT_1;GSYM drop;LIFT_DROP;DROP_VEC;REAL_MUL_RID] THEN REAL_ARITH_TAC);;

let BALLBOT_DYNAMICS_XOY = prove
 (`!q t0 t1 Mt It Ib l r fai fai' fai'' delta delta' delta'' q q' q'' t.
  drop t0 < drop t1 /\ interval[t0,t1] = s /\ t IN s /\
  {u:real^(2,1)finite_sum | ?y. y IN mspace(fspace s) /\ u IN IMAGE y s} = s0 /\
  {u:real^(2,2)finite_sum | ?y. y IN mspace(fspace s) /\ u IN IMAGE y s} = s1 /\
  q = (\t. vector[drop(fai t); drop(delta t)]:real^2) /\
  q' = (\t. vector[drop(fai' t); drop(delta' t)]:real^2) /\
  q'' = (\t. vector[drop(fai'' t); drop(delta'' t)]:real^2) /\
  (!t. t IN s ==> (fai has_vector_derivative fai' t)(at t within s)) /\
  (!t. t IN s ==> (delta has_vector_derivative delta' t)(at t within s)) /\
  (!t. t IN s ==> (fai' has_vector_derivative fai'' t)(at t within s)) /\
  (!t. t IN s ==> (delta' has_vector_derivative delta'' t)(at t within s)) /\
  ke = (\u:real^(2,2)finite_sum. lift((&1 / &2 * (Ib) * sndcart u$1 * sndcart u$1) + (&1 / &2 * (It) * sndcart u$2 * sndcart u$2))) /\
  ue = (\u:real^2. lift(&0)) /\
  alpha = Ib + (Mb + Mt) * r * r /\ beta = Mt * r * l /\ gamma = It + Mt * l * l /\ mu = Mt * g * l /\
  M = vector [vector[Ib;&0]:real^2;vector[&0; It]:real^2]:real^2^2 /\
  f = (\t:real^1.(vector[lift(&0);lift(tau)]:real^1^2))/\
  rr =(\u:real^(2,1)finite_sum. (vector[lift(fstcart u$1);lift(fstcart u$2)]:real^1^2))/\
  lagrange_equations_autonomous s s0 s1 ke ue q f rr t
  ==> M ** (q'' t) = vector [&0; tau]`,
  INTRO_TAC "! * ; dropt s t s0 s1 q q' q'' faidif deltadif fai'dif delta'dif ke ue alpha beta gamma mu M f rr lagrange" THEN
  CLAIM_TAC "vd_q"
  `!t. t IN s ==> (vector_derivative (q:real^1->real^2) (at t within s) =  ((q' (t:real^1)):real^2))` THENL
  [REPEAT STRIP_TAC THEN EXPAND_TAC "s" THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN STRIP_TAC THEN
  ASM_SIMP_TAC[] THEN SIMP_TAC[has_vector_derivative] THEN ONCE_REWRITE_TAC[HAS_DERIVATIVE_COMPONENTWISE_WITHIN]
  THEN SIMP_TAC[FORALL_2;DIMINDEX_2] THEN HYP SIMP_TAC "q q'"[] THEN SIMP_TAC[VECTOR_2;LIFT_DROP;ETA_AX] THEN
  USE_THEN "faidif" MP_TAC THEN SIMP_TAC[VECTOR_MUL_COMPONENT;VECTOR_2] THEN SIMP_TAC[LIFT_CMUL;LIFT_DROP] THEN
  SIMP_TAC[has_vector_derivative] THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN USE_THEN "deltadif" MP_TAC THEN SIMP_TAC[has_vector_derivative] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  ABBREV_TAC
  `ke' =(\t:real^1. (\h:real^(2,2)finite_sum. lift(&1 / &2 * Ib * ((sndcart (qdq s (q:real^1->real^2) t)$1 * sndcart h$1)
  +(sndcart h$1 * sndcart (qdq s (q:real^1->real^2) t)$1))) + lift(&1 / &2 * It * ((sndcart (qdq s (q:real^1->real^2) t)$2 * sndcart h$2) +
  (sndcart h$2 * sndcart (qdq s (q:real^1->real^2) t)$2)))))` THEN
  CLAIM_TAC "kedif"
  `!t. t IN s ==> ((ke:real^(2,2)finite_sum->real^1) has_derivative ke' t)(at (qdq s (q:real^1->real^2) t) within s1)` THENL[
  REPEAT STRIP_TAC THEN HYP SIMP_TAC "ke"[] THEN EXPAND_TAC "ke'" THEN SIMP_TAC[LIFT_ADD] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL[SIMP_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN SIMP_TAC[GSYM LIFT_CMUL] THEN SIMP_TAC[LIFT_ADD] THEN
  MP_TAC (ISPECL [`(\u:real^(2,2)finite_sum. sndcart u$1)`;`(\h:real^(2,2)finite_sum. (sndcart h$1))`;`(\u:real^(2,2)finite_sum. lift (sndcart u$1))`;`(\h:real^(2,2)finite_sum. lift((sndcart h$1)))`;`(qdq s (q:real^1->real^2) t')`;`s1:real^(2,2)finite_sum->bool`] HAS_DERIVATIVE_MUL_WITHIN) THEN SIMP_TAC[o_DEF] THEN ANTS_TAC THENL
  [SIMP_TAC[DIMINDEX_2;ARITH;SNDCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT];ALL_TAC] THEN SIMP_TAC[GSYM LIFT_CMUL];ALL_TAC] THEN SIMP_TAC[LIFT_CMUL] THEN MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN
  MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN SIMP_TAC[GSYM LIFT_CMUL] THEN SIMP_TAC[LIFT_ADD] THEN
  MP_TAC (ISPECL [`(\u:real^(2,2)finite_sum. sndcart u$2)`;`(\h:real^(2,2)finite_sum. (sndcart h$2))`;`(\u:real^(2,2)finite_sum. lift (sndcart u$2))`;`(\h:real^(2,2)finite_sum. lift((sndcart h$2)))`;`(qdq s (q:real^1->real^2) t')`;`s1:real^(2,2)finite_sum->bool`] HAS_DERIVATIVE_MUL_WITHIN) THEN
  SIMP_TAC[o_DEF] THEN ANTS_TAC THENL
  [SIMP_TAC[DIMINDEX_2;ARITH;SNDCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT];ALL_TAC] THEN SIMP_TAC[GSYM LIFT_CMUL];ALL_TAC] THEN
  ABBREV_TAC `ue' =(\t:real^1. (\h:real^2. lift(&0)))` THEN
  ABBREV_TAC `s2 = {u:real^2 | ?y. y IN mspace(fspace s) /\ u IN IMAGE y s}` THEN
  CLAIM_TAC "uedif"
  `!t. t IN s ==> ((ue:real^2->real^1) has_derivative ue' t)(at (q (t:real^1)) within s2)` THENL[
  REPEAT STRIP_TAC THEN HYP SIMP_TAC "ue"[] THEN EXPAND_TAC "ue'" THEN SIMP_TAC[LIFT_NUM] THEN
  SIMP_TAC[HAS_DERIVATIVE_CONST];ALL_TAC] THEN
  CLAIM_TAC "ke_sub_ue_dif"
  `!t. t IN s ==>((\u:real^(2,2)finite_sum. ((ke u - ue (fstcart u)):real^1)) has_derivative
  ((\h:real^(2,2)finite_sum. (ke' t h - ue' t (fstcart h))):real^(2,2)finite_sum->real^1)) (at (qdq s (q:real^1->real^2) t) within s1)` THENL[
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_DERIVATIVE_SUB THEN CONJ_TAC THENL[SIMP_TAC[ETA_AX] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  HYP SIMP_TAC "ue"[] THEN EXPAND_TAC "ue'" THEN SIMP_TAC[LIFT_NUM] THEN SIMP_TAC[HAS_DERIVATIVE_CONST];ALL_TAC] THEN
  CLAIM_TAC "fretlag"
  `!t. t IN s ==> frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) (ue:real^2->real^1)) (at (qdq (s:real^1->bool) (q:real^1->real^2) t) within (s1:real^(2,2)finite_sum->bool)) = (\t:real^1.(\h:real^(2,2)finite_sum. ke' t h - ue' t (fstcart h)):real^(2,2)finite_sum->real^1) t` THENL [
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN
  MAP_EVERY EXISTS_TAC[`(lagrange_function_autonomous ke ue):real^(2,2)finite_sum->real^1`;`qdq s (q:real^1->real^2) t'`;
                       `s1:real^(2,2)finite_sum->bool`] THEN SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN
  REWRITE_TAC[lagrange_function_autonomous] THEN CONJ_TAC THENL [ASM_MESON_TAC[differentiable];ALL_TAC] THEN CONJ_TAC THENL
  [HYP SIMP_TAC "ke_sub_ue_dif"[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN INTRO_TAC "![k] [e]; k1 kQQ1 e" THEN EXISTS_TAC `e / &2` THEN
  HYP SIMP_TAC "e" [REAL_ARITH`&0 < e ==> &0 < abs(e / &2) /\ abs(e / &2) < e`] THEN SIMP_TAC[qdq_def;fpt;fun_map_2] THEN EXPAND_TAC "s1" THEN EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM;IN_IMAGE;FSPACE;COMPACT_INTERVAL] THEN
  EXISTS_TAC `\t:real^1. if t IN interval[t0,t1] then
  pastecart (q t' :real^2) (higher_vector_derivative 1 q s t' :real^2) + e / &2 % basis k else vec 0` THEN SIMP_TAC[continuous_on] THEN SIMP_TAC[GSYM continuous_on] THEN CONJ_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN  SIMP_TAC[CONTINUOUS_ON_CONST;CONTINUOUS_ON_THREE_FPT] ;ALL_TAC] THEN
  EXISTS_TAC `t':real^1` THEN HYP SIMP_TAC "s"[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CLAIM_TAC "fcu_hd"
  `((\u:real^(2,1)finite_sum. lift(fstcart u$2)) has_derivative (\u:real^(2,1)finite_sum. lift(fstcart u$2))) (at (qt (q:real^1->real^2)  (t:real^1)) within (s0:real^(2,1)finite_sum->bool))` THENL
  [SIMP_TAC[DIMINDEX_2;ARITH;FSTCART_COMPONENT] THEN SIMP_TAC[HAS_DERIVATIVE_LIFT_COMPONENT] ;ALL_TAC] THEN
  CLAIM_TAC "fd_u2"
  `frechet_derivative (\u:real^(2,1)finite_sum. lift (fstcart u$2)) (at (qt (q:real^1->real^2) (t:real^1)) within (s0:real^(2,1)finite_sum->bool)) = (\u:real^(2,1)finite_sum. lift(fstcart u$2))` THENL[
  MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_WITHIN THEN MAP_EVERY EXISTS_TAC[`(\u:real^(2,1)finite_sum. lift (fstcart u$2))`;
                                      `(qt (q:real^1->real^2) (t:real^1))`;`s0:real^(2,1)finite_sum->bool`] THEN
  SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS] THEN CONJ_TAC THENL [ASM_MESON_TAC[differentiable];ALL_TAC] THEN
  HYP SIMP_TAC "fcu_hd"[] THEN INTRO_TAC "![k] [e]; k1 kQQ1 e" THEN EXISTS_TAC `e / &2` THEN
  HYP SIMP_TAC "e" [REAL_ARITH`&0 < e ==> &0 < abs(e / &2) /\ abs(e / &2) < e`] THEN SIMP_TAC[qt_def;fpt;fun_map_2] THEN
  EXPAND_TAC "s0" THEN EXPAND_TAC "s" THEN SIMP_TAC[IN_ELIM_THM;IN_IMAGE;FSPACE;COMPACT_INTERVAL] THEN
  EXISTS_TAC `\t':real^1. if t' IN interval[t0,t1] then
  pastecart (q t:real^2) (t:real^1) + e / &2 % basis k else vec 0` THEN SIMP_TAC[continuous_on] THEN SIMP_TAC[GSYM continuous_on]
  THEN CONJ_TAC THENL
  [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN  SIMP_TAC[CONTINUOUS_ON_CONST;CONTINUOUS_ON_THREE_FPT] ;ALL_TAC] THEN
  EXISTS_TAC `t:real^1` THEN HYP SIMP_TAC "s"[] THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  CLAIM_TAC "sq1"
  `(!t. t IN s ==> sndcart(qdq (s:real^1->bool) (q:real^1->real^2) t)$1 = drop (fai' t))`THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;SNDCART_PASTECART] THEN SIMP_TAC[num_CONV `1`; higher_vector_derivative;vector_fun_derivative;GSYM vector_derivative] THEN
  SIMP_TAC[ARITH_RULE`SUC 0 = 1`] THEN HYP SIMP_TAC "vd_q q'"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  CLAIM_TAC "sq2"
  `(!t. t IN s ==> sndcart (qdq (s:real^1->bool) (q:real^1->real^2) t)$2 = drop (delta' t))` THENL
  [SIMP_TAC[qdq_def;fpt;fun_map_2;SNDCART_PASTECART] THEN SIMP_TAC[num_CONV `1`; higher_vector_derivative;vector_fun_derivative;GSYM vector_derivative] THEN
  SIMP_TAC[ARITH_RULE`SUC 0 = 1`] THEN HYP SIMP_TAC "vd_q q'"[] THEN SIMP_TAC[VECTOR_2]; ALL_TAC] THEN
  SIMP_TAC[CART_EQ;DIMINDEX_2;FORALL_2] THEN CONJ_TAC THENL[
  USE_THEN "lagrange" MP_TAC THEN REWRITE_TAC[lagrange_equations_autonomous] THEN DISCH_THEN(MP_TAC o SPEC`1`) THEN SIMP_TAC[IN_NUMSEG;DIMINDEX_2;ARITH] THEN
  HYP SIMP_TAC "M q' q'' alpha beta gamma mu"[] THEN
  REWRITE_TAC[VECTOR_ADD_COMPONENT;VECTOR_2] THEN SIMP_TAC[DIMINDEX_GE_1;LE_REFL;MATRIX_VECTOR_MUL_COMPONENT;DOT_2;VECTOR_2]
  THEN SIMP_TAC[jacobian;CART_EQ;DIMINDEX_1;FORALL_1;VECTOR_SUB_COMPONENT;LIFT_COMPONENT;TRANSP_COMPONENT] THEN
  SIMP_TAC[REAL_MUL_LZERO;REAL_ADD_RID] THEN HYP SIMP_TAC "ke_sub_ue_dif fretlag"[] THEN
  CLAIM_TAC "matrix_fretlag"
  `(matrix(frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) ue)
  (at (qdq s (q:real^1->real^2) t) within s1)))$1$1 = &0` THENL [
  HYP SIMP_TAC "fretlag t"[] THEN EXPAND_TAC "ke'" THEN EXPAND_TAC "ue'"  THEN SIMP_TAC[MATRIX_COMPONENT;DIMINDEX_GE_1;LE_REFL] THEN
  SIMP_TAC[VECTOR_MUL_LZERO;VECTOR_ADD_LID;FSTCART_COMPONENT;BASIS_COMPONENT;DIMINDEX_GE_1;LE_REFL;SNDCART_COMPONENT;DIMINDEX_2;
  ARITH_RULE `1<=2`;ARITH;DIMINDEX_FINITE_SUM;LIFT_NUM;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;
  VECTOR_MUL_RZERO;VECTOR_ADD_COMPONENT;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;VECTOR_ADD_RID;VEC_COMPONENT;LIFT_COMPONENT;
  REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;DROP_CMUL;LIFT_DROP] THEN REAL_ARITH_TAC;ALL_TAC] THEN
  CLAIM_TAC "vd_tmfl"
  `vector_derivative (\t. transp(matrix
  (frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) (ue:real^2->real^1))
  (at (qdq (s:real^1->bool) (q:real^1->real^2) t) within (s1:real^(2,2)finite_sum->bool))))$3)
  (at t within s) =  Ib % fai'' t` THENL[
  EXPAND_TAC "s" THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN HYP SIMP_TAC "dropt s t"[] THEN
  SIMP_TAC[HAS_VECTOR_REAL_DERIVATIVE_WITHIN;o_DEF;drop;TRANSP_COMPONENT;MATRIX_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_2;ARITH]
  THEN SIMP_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN;o_DEF;LIFT_DROP;LIFT_COMPONENT] THEN SIMP_TAC[GSYM drop;LIFT_DROP;GSYM IMAGE_o;o_DEF;IMAGE_ID] THEN HYP SIMP_TAC "t fretlag" [has_vector_derivative;HAS_DERIVATIVE_WITHIN] THEN SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN;GSYM has_vector_derivative] THEN EXPAND_TAC "ke'" THEN EXPAND_TAC "ue'" THEN SIMP_TAC[has_vector_derivative] THEN SIMP_TAC[HAS_DERIVATIVE_WITHIN_ALT] THEN HYP SIMP_TAC "t sq1 sq2"[] THEN SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN_ALT] THEN
  SIMP_TAC[GSYM has_vector_derivative] THEN SIMP_TAC[FSTCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[SNDCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[BASIS_COMPONENT;DIMINDEX_GE_1;DIMINDEX_FINITE_SUM;DIMINDEX_1;DIMINDEX_2;LE_REFL;ARITH] THEN
  SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
  SIMP_TAC[REAL_ADD_LID;REAL_MUL_RZERO;LIFT_NUM;VECTOR_ADD_RID;VECTOR_SUB_RZERO] THEN
  SIMP_TAC[LIFT_CMUL] THEN
  SUBGOAL_THEN
  `(\t:real^1. &1 / &2 % Ib % lift (drop (fai' t) + drop (fai' t))) = (\t:real^1. (Ib % (fai' t)))`SUBST1_TAC THENL
  [SIMP_TAC[FUN_EQ_THM] THEN INTRO_TAC "![t']" THEN SIMP_TAC[LIFT_ADD;LIFT_DROP] THEN VECTOR_ARITH_TAC;ALL_TAC]
  THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  HYP SIMP_TAC "vd_tmfl matrix_fretlag"[] THEN SIMP_TAC[REAL_SUB_RZERO] THEN HYP SIMP_TAC "f rr"[] THEN SIMP_TAC[generalized_forces] THEN SIMP_TAC[LAMBDA_BETA;DIMINDEX_2;ARITH] THEN SIMP_TAC[SUM_2;VECTOR_2;LIFT_NUM;DOT_LZERO;REAL_ADD_LID] THEN
  HYP SIMP_TAC "fd_u2"[] THEN SIMP_TAC[FSTCART_COMPONENT;LE_REFL;DIMINDEX_2;ARITH] THEN SIMP_TAC[BASIS_COMPONENT;LE_REFL;DIMINDEX_FINITE_SUM;DIMINDEX_1;
  DIMINDEX_2;ARITH] THEN  SIMP_TAC[DOT_1;GSYM drop;LIFT_DROP;DROP_VEC;REAL_MUL_RID;REAL_MUL_RZERO] THEN SIMP_TAC[GSYM drop;DROP_CMUL] ;ALL_TAC] THEN USE_THEN "lagrange" MP_TAC THEN REWRITE_TAC[lagrange_equations_autonomous] THEN DISCH_THEN(MP_TAC o SPEC`2`) THEN SIMP_TAC[IN_NUMSEG;DIMINDEX_2;ARITH] THEN HYP SIMP_TAC "M q' q'' alpha beta gamma mu"[] THEN REWRITE_TAC[VECTOR_ADD_COMPONENT;VECTOR_2] THEN SIMP_TAC[DIMINDEX_2;ARITH;MATRIX_VECTOR_MUL_COMPONENT;DOT_2;VECTOR_2;REAL_ADD_RID;REAL_MUL_LZERO] THEN
  SIMP_TAC[jacobian;CART_EQ;DIMINDEX_1;FORALL_1;VECTOR_SUB_COMPONENT;LIFT_COMPONENT;TRANSP_COMPONENT;REAL_ADD_LID] THEN
  HYP SIMP_TAC "ke_sub_ue_dif fretlag"[] THEN
  CLAIM_TAC "matrix_fretlag"
  `(matrix(frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) ue)
  (at (qdq s (q:real^1->real^2) t) within s1)))$1$2 = &0`THENL
  [HYP SIMP_TAC "fretlag t"[] THEN EXPAND_TAC "ke'" THEN EXPAND_TAC "ue'"  THEN
  SIMP_TAC[MATRIX_COMPONENT;DIMINDEX_GE_1;DIMINDEX_FINITE_SUM;DIMINDEX_2;ARITH] THEN
  SIMP_TAC[VECTOR_MUL_LZERO;VECTOR_ADD_LID;FSTCART_COMPONENT;BASIS_COMPONENT;DIMINDEX_GE_1;LE_REFL;SNDCART_COMPONENT;DIMINDEX_2;
  ARITH_RULE `1<=2`;ARITH;DIMINDEX_FINITE_SUM;LIFT_NUM;REAL_MUL_LID;REAL_MUL_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;
  VECTOR_MUL_RZERO;VECTOR_ADD_COMPONENT;VECTOR_SUB_COMPONENT;VECTOR_MUL_COMPONENT;VECTOR_ADD_RID;VEC_COMPONENT;LIFT_COMPONENT;
  REAL_ADD_LID;REAL_ADD_RID;REAL_MUL_LZERO;REAL_MUL_RZERO;DROP_CMUL;LIFT_DROP] THEN REAL_ARITH_TAC;ALL_TAC] THEN
  CLAIM_TAC "vd_tmfl"
  `vector_derivative (\t. transp(matrix
  (frechet_derivative (lagrange_function_autonomous (ke:real^(2,2)finite_sum->real^1) (ue:real^2->real^1))
  (at (qdq (s:real^1->bool) (q:real^1->real^2) t) within (s1:real^(2,2)finite_sum->bool))))$4)
  (at t within s) =  It % delta'' t` THENL
  [EXPAND_TAC "s" THEN MATCH_MP_TAC VECTOR_DERIVATIVE_WITHIN_CLOSED_INTERVAL THEN HYP SIMP_TAC "dropt s t"[] THEN
  SIMP_TAC[HAS_VECTOR_REAL_DERIVATIVE_WITHIN;o_DEF;drop;TRANSP_COMPONENT;MATRIX_COMPONENT;DIMINDEX_FINITE_SUM;DIMINDEX_2;ARITH]
  THEN SIMP_TAC[HAS_REAL_VECTOR_DERIVATIVE_WITHIN;o_DEF;LIFT_DROP;LIFT_COMPONENT] THEN SIMP_TAC[GSYM drop;LIFT_DROP;GSYM IMAGE_o;o_DEF;IMAGE_ID] THEN HYP SIMP_TAC "t fretlag" [has_vector_derivative;HAS_DERIVATIVE_WITHIN] THEN SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN;GSYM has_vector_derivative] THEN EXPAND_TAC "ke'" THEN EXPAND_TAC "ue'" THEN
  SIMP_TAC[has_vector_derivative] THEN SIMP_TAC[HAS_DERIVATIVE_WITHIN_ALT] THEN HYP SIMP_TAC "t sq1 sq2"[] THEN
  SIMP_TAC[GSYM HAS_DERIVATIVE_WITHIN_ALT] THEN SIMP_TAC[GSYM has_vector_derivative] THEN
  SIMP_TAC[FSTCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[SNDCART_COMPONENT;DIMINDEX_GE_1;DIMINDEX_2;ARITH;LE_REFL] THEN
  SIMP_TAC[BASIS_COMPONENT;DIMINDEX_GE_1;DIMINDEX_FINITE_SUM;DIMINDEX_1;DIMINDEX_2;LE_REFL;ARITH] THEN
  SIMP_TAC[REAL_MUL_LZERO;REAL_MUL_RZERO;REAL_MUL_LID;REAL_MUL_RID] THEN
  SIMP_TAC[REAL_ADD_LID;REAL_MUL_RZERO;LIFT_NUM;VECTOR_ADD_RID;VECTOR_SUB_RZERO] THEN
  SIMP_TAC[LIFT_CMUL;VECTOR_ADD_LID] THEN
  SUBGOAL_THEN
  `(\t:real^1. &1 / &2 % It % lift (drop (delta' t) + drop (delta' t))) = (\t:real^1. (It % (delta' t)))` SUBST1_TAC THENL
  [SIMP_TAC[FUN_EQ_THM] THEN INTRO_TAC "![t']" THEN SIMP_TAC[LIFT_ADD;LIFT_DROP] THEN VECTOR_ARITH_TAC;ALL_TAC]
  THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_CMUL THEN ASM_SIMP_TAC[];ALL_TAC] THEN
  HYP SIMP_TAC "vd_tmfl matrix_fretlag"[] THEN SIMP_TAC[REAL_SUB_RZERO] THEN
  HYP SIMP_TAC "f rr"[] THEN SIMP_TAC[generalized_forces] THEN
  SIMP_TAC[LAMBDA_BETA;DIMINDEX_2;ARITH] THEN
  SIMP_TAC[SUM_2;VECTOR_2;LIFT_NUM;DOT_LZERO;REAL_ADD_LID] THEN
  HYP SIMP_TAC "fd_u2"[] THEN SIMP_TAC[FSTCART_COMPONENT;LE_REFL;DIMINDEX_2;ARITH] THEN
  SIMP_TAC[BASIS_COMPONENT;LE_REFL;DIMINDEX_FINITE_SUM;DIMINDEX_1;
  DIMINDEX_2;ARITH] THEN SIMP_TAC[DOT_1;GSYM drop;LIFT_DROP;DROP_VEC;REAL_MUL_RID;REAL_MUL_RZERO] THEN SIMP_TAC[GSYM drop;DROP_CMUL]);;

(* ------------------------------------------------------------------------- *)
(* complementary theorem.                                                    *)
(* ------------------------------------------------------------------------- *)

let HAS_VECTOR_REAL_DERIVATIVE_WITHIN = prove
 (`!f f' x s. (f has_vector_derivative f') (at x within s) <=>
  ((drop o f o lift) has_real_derivative (drop f')) (atreal (drop x) within (IMAGE drop s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_vector_derivative; HAS_REAL_FRECHET_DERIVATIVE_WITHIN]
  THEN SIMP_TAC[o_DEF;LIFT_DROP;ETA_AX;IMAGE_ID;GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC
  THEN SIMP_TAC[FUN_EQ_THM;CART_EQ;DIMINDEX_1;FORALL_1;VECTOR_MUL_COMPONENT;REAL_MUL_SYM;drop]);;

let VECTOR_ADD_TEQ = VECTOR_ARITH `!x y z:real^N. y + x = z + x <=> y = z`;;

let CROSS_RMUL2 = prove
 (`!c x y. c % x cross y = x cross (c % y)`,
  VEC3_TAC);;








