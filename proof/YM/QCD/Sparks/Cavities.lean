import YM.QCD.Sparks.Scribe

/-! # realization rooted birth. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sparks
open Function Filter Lattice Wilson Lat Kit Finset Eyrie Quarry Rudder Stationary Run
open YM.Further.PhysicalPeriodLimitF933 Macrame Exterior Flume Work.F03 Revolve RG
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {n:Side}{b k:ℕ}{r C:ℝ}{I:Type}
lemma cellsRay (W:Bloom k)(x : Cnr n)(y:Site n): Run.cell (epilogue W x) 0 y=if wrap n (stop 0 W.tail)=y then (occ (0:Site n) (stop 0 W.tail)) • lepton W x 0 else 0 := by
  ext i j; change entryR (U:=1) _ _ _ _ = _; unfold entryR; dsimp only; rw [wrap_stop,zero_add]; split; swap; rfl
  rw [rack,occ_rays,Matrix.mul_smul,Matrix.mul_one]

def frameR (p:Tilt k)(K:Typewriter k)(x:Cnr n)(y:Site n):= if wrap n p.1=y then (∏ i, idyllic (p.2 i) x) • (occ (0:Site n) p.1 • K p) else 0
def frameX (i: Rim k)(j: Ryde i)(K:Typewriter k)(x:Cnr n)(z: Site n):=(k.factorial:ℝ) • Run.cell (epilogue (rivet K ⟨i,j⟩) x) 0 z
lemma groupR (K:Typewriter k)(x:Cnr n)(y:Site n)(i:Rim k):
    ∑ p: Ryde i,frameX i p K x y= ∑ j:Fin k→su.ColorIndex,frameR (raise i j) K x y := by
  let V:= Lattice.wrap n i.1; let M(p:Ryde i):=rivet K ⟨i,p⟩
  have ht p:stop 0 (M p).tail=i.1:=rad_plan _
  let W:=occ (0:Site n) i.1
  by_cases he : V=y
  swap
  · unfold frameX; simp_rw [cellsRay,show ∀ p,stop 0 (rivet K ⟨i,p⟩).tail=_ from ht]; change ∑ p:Ryde i,_ • (if V=y then _ else 0)=_; simp only [if_neg he,smul_zero,sum_const_zero]; symm; refine sum_eq_zero fun p _=> ?_; exact if_neg he
  subst y
  let U (p : Ryde i) (j:Fin k→su.ColorIndex)(a : Fin k):= faceCurl (slotFace ((M p).petals a) (0:Site n)) (arm su n 1 x) (j a)
  let d (p: Ryde i)(j:Fin k→su.ColorIndex):= ∏ a, (plant (i.2 a) (p a)).sign * U p j a
  have hz p:frameX i p K x V=∑ j:Fin k→su.ColorIndex, d p j • (W • K (raise i j)):= by
    unfold frameX; rw [cellsRay]; change _ • (if wrap n (stop _ (M p).tail)=_ then _ else _) = _; simp only [if_pos (show wrap n _=V from congr_arg _ (ht p))]; unfold lepton Bloom.hues
    simp_rw [Finset.smul_sum]; refine sum_congr rfl (fun j _ => ?_)
    change (k.factorial:ℝ) • (occ (0:Site n) (stop _ (M p).tail) • (((↑(∏ a, U p j a)):ℂ) • ((signal i p:ℂ) • _))) = _
    rw [ht]; unfold d; rw [Finset.prod_mul_distrib]; -- coe smul bridge
    have hs (b:ℝ)(B:Bundle): b • B=(↑b:ℂ) • B:=rfl
    rw [hs, hs (Finset.prod _ _ * _)]
    simp only [smul_smul]; congr 1; unfold signal W; push_cast; field_simp [show (↑k.factorial:ℂ)≠0 by exact_mod_cast k.factorial_ne_zero]
  simp_rw [hz]; rw [Finset.sum_comm]; apply sum_congr rfl; intro j _; rw [← Finset.sum_smul]; unfold frameR; rw [if_pos (show wrap n (raise i j).1=V from rfl)]
  congr 1
  have hp (a:Fin k) := field ((raise i j).2 a) x; -- simplify
  let c (a:Fin k)(z:Get (i.2 a)):= (plant (i.2 a) z).sign*faceCurl (slotFace (shop (plant (i.2 a) z)) (0:Site n)) (arm su n 1 x) (j a)
  rw [show ∏ a,idyllic ((raise i j).2 a) x=∏ a,∑ z:Get (i.2 a),c a z from Finset.prod_congr rfl fun a _=> field ..]; exact (Fintype.prod_sum c).symm

lemma plain_pay (K:Typewriter k) (h:∀ i, ‖K i‖≤C*aim r i) (he:0≤C)(hp:0<r) (x:Cnr n)(y:Site n): Summable (fun i=>‖frameR i K x y‖):=by
  let U:= fun i:Tilt k=> C*(2*‖x‖)^k*((1+timbre i:ℝ)^k* aim r i)
  have hu : Summable U:=(beam_use k hp).mul_left _
  apply hu.of_nonneg_of_le (fun i=>norm_nonneg _); intro i; unfold frameR U; split <;> rename_i he'
  · let z (q:Nub) := q.1
    have hh j : ‖idyllic (i.2 j) x‖≤ 2*‖x‖*(1+timbre i):= by
      let p:Stock := ((i.2 j).1,(i.2 j).2.1); have hv:=paid_page x (i.2 j).2.2 0 (stanza p); apply hv.trans
      have hx : (↑(stanza p).length:ℝ)≤2* Laurent.size p.1 + 2:= by exact_mod_cast stanza_length p
      have hg : Laurent.size p.1 ≤ timbre i:= le_trans (single_le_sum (fun j _=> Nat.zero_le (Laurent.size (i.2 j).1)) (mem_univ j)) (Nat.le_add_left ..)
      apply (mul_le_mul_of_nonneg_right (hx.trans (show 2*(_ : ℝ)+2 ≤ 2*timbre i+2 by gcongr)) (norm_nonneg _)).trans_eq; ring
    rw [norm_smul,norm_smul,pathLength,one_mul,norm_prod];
    apply (mul_le_mul (prod_le_prod (s:=univ) (fun j _=>norm_nonneg (idyllic (i.2 j) x)) (fun j _=> hh j)) (h i) (norm_nonneg _) (prod_nonneg (fun _ _=> by positivity))).trans_eq; rw [prod_const,card_univ,Fintype.card_fin,mul_pow (2*‖x‖) (1+_)]; ring
  rw [norm_zero]; have hh:=aim_pos r i; positivity
end YM.QCD.Sparks
