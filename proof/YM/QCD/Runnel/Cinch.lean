import YM.QCD.Runnel.Shirt
import YM.QCD.Cedar.Canopy

/-! # path-tail heritage, arbitrary b -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Run
open Lat Cost Lattice Wilson Function Filter Finset Kit Pine Flume Laurent Metric
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
variable {f : Side} (t : Site f) {δ b c C : ℝ} {n r B p : ℕ}
lemma amounts (x : Cover) (o : Lattice.Order): (route 0 x o).length=size x := by
  have he (v : List Axis): (axisRoute 0 x v).length=(v.map fun i=>(x i).natAbs).sum:=by
    induction v with
    | nil=>rfl
    | cons a v ih=>
      rw [show axisRoute 0 _ (a::v)=straight a (x a-0)++axisRoute 0 x v from rfl,List.length_append,ih,List.map_cons,List.sum_cons]; simp [straight]
  unfold route allAxes; rw [he,List.map_map, ← List.ofFn_eq_map,List.sum_ofFn]; exact Equiv.sum_comp o (fun i=> (x i).natAbs)
lemma motive (x : Cover) (hb : 0≤b) (hd : 0<δ) (hc : 0<c) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (c*n)): Pride δ b B (fun U=>mote t U x) (Real.exp (c*n)*Real.exp (c*size x)):=by
  let M (o:Lattice.Order) (U:Grid f):= routeM t U (route 0 x o); let C:=Real.exp (c*n)*Real.exp (c*size x)
  have he o:Pride δ b B (M o) C:=by simpa only [amounts] using Pride.trail (b:=b) t (route 0 x o) hb hd hc hr ht hg
  have hh:=((Pride.group univ fun o _=>he o).scale (votes:ℂ)⁻¹)
  rw [show (fun U=>mote t U x)=(votes:ℂ)⁻¹ • ∑ i,M i from funext fun U=> by unfold mote; rw [Pi.smul_apply,Finset.sum_apply]]
  rw [norm_inv,Complex.norm_natCast,sum_const,card_univ,nsmul_eq_mul,← mul_assoc, inv_mul_cancel₀ poll_pos.ne',one_mul] at hh; exact hh
lemma Width.filtered (T : Cover→ℝ) (h : Width (2*c) C T) (hx : ℕ) (hc : 0≤c):
    Width c (C*Real.exp (-c*hx)) (fun i=> if size i ≤ hx then 0 else T i):=by
  let g (i:Cover):= if size i≤hx then 0 else T i
  have ht: Summable (fun i : Cover => Real.exp (2*c*size i)*‖T i‖*Real.exp (-c*hx)):=h.2.1.mul_right _
  have he (i: Cover): Real.exp (c*size i)*‖g i‖ ≤ Real.exp (2*c*size i)*‖T i‖*Real.exp (-c*hx):=by
    unfold g; split; · rw [norm_zero,mul_zero]; positivity
    next hi=> rw [mul_right_comm,← Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_le_exp.mpr; push Not at hi; nlinarith [mul_le_mul_of_nonneg_left (show (hx:ℝ) ≤ size i from by exact_mod_cast hi.le) hc]
  have hu : Summable (fun i: Cover=> Real.exp (c*size i)*‖g i‖):=ht.of_nonneg_of_le (fun i=>by positivity) he
  refine ⟨fun i=> mul_nonneg (Real.exp_pos _).le (norm_nonneg _),hu,(hu.tsum_le_tsum he ht).trans ?_⟩
  rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right h.2.2 (by positivity)
lemma lodge (a : Cover→ℝ) (hw : Width c C a) (hb : 0≤b) (hd : 0<δ) (hc : 0<c) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (c*n)): Pride δ b B (fun U=>deck t U a) (C*Real.exp (c*n)):=by
  let M (x : Cover) (U : Grid f):= mote t U x
  let R:= Real.exp (c*n)
  have he (x : Cover):Pride δ b B ((a x:ℂ) • M x) (Real.exp (c*size x)*‖a x‖* R):=by
    rw [show Real.exp _*‖a x‖*R= ‖(a x:ℂ)‖*(Real.exp (c*n)*Real.exp (c*size x)) by rw [Complex.norm_real]; unfold R; ring]; exact (motive t x hb hd hc hr ht hg).scale _
  have hz : Summable (fun x=>Real.exp (c*size x)*‖a x‖*R):=hw.2.1.mul_right _
  exact (Pride.hotel (M:=fun U=> deck t U a) hd hb hz he (fun U=> (motes ((hw.unweighted hc.le).2.1) t U).of_norm.hasSum)).mono (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hw.2.2 (Real.exp_pos _).le)

def corto (a : Cover→ℝ) (p:ℕ) (x:Cover):= if size x≤p then a x else 0
lemma Width.short (a : Cover→ℝ) (p) (h : Width c C a): Width c C (corto a p):=by
  have he i : Real.exp (c*size i)*‖corto a p i‖ ≤ Real.exp (c*size i)*‖a i‖:=by
    unfold corto; split; · exact le_rfl
    rw [norm_zero,mul_zero]; positivity
  have hh : Summable (fun i => Real.exp (c*size i)*‖corto a p i‖):=h.2.1.of_nonneg_of_le (fun i=>by positivity) he
  exact ⟨fun i=>by positivity,hh,(hh.tsum_le_tsum he h.2.1).trans h.2.2⟩
lemma lodge_minus (a b : Cover→ℝ) (ha : Summable fun i=> ‖a i‖) (hb : Summable fun i=> ‖b i‖):
    (fun U=>deck t U (a-b))=(fun U=> deck t U a)-(fun U=> deck t U b):=by
  funext U; simp only [Pi.sub_apply,deck,Complex.ofReal_sub,sub_smul]; rw [Summable.tsum_sub ((motes ha t U).of_norm) ((motes hb t U).of_norm)]

def clog (p:ℕ): Finset Cover := (box p).filter fun x=> size x≤ p -- inspect
lemma clogs (x:Cover) : x∈clog p ↔ size x≤p:=by
  rw [clog,mem_filter,and_iff_right_of_imp]; intro h; rw [box_test]
  have hh (i : Axis) : (x i).natAbs ≤ p:= (single_le_sum (fun j _=>Nat.zero_le (x j).natAbs) (mem_univ i)).trans h
  exact ⟨fun i=>by have ht:=hh i; omega,fun i=>by have ht:=hh i; omega⟩
lemma plea (a : Cover→ℝ) : Reads eye eye (2*p) (fun U=> deck t U (corto a p)):=by
  let M (x:Cover) (U : Grid f):=(corto a p x:ℂ) • mote t U x
  rw [show (fun U=>_)=∑ x∈clog p,M x from ?_]
  · apply Reads.count; intro i hi; refine Reads.coin ?_ _
    unfold mote; refine Reads.coin (Reads.collect fun o=> (membership t _).dilate ?_) _; rw [amounts]; exact Nat.mul_le_mul_left _ ((clogs i).mp hi)
  funext U; rw [Finset.sum_apply]; unfold deck; rw [tsum_eq_sum]; exact fun i hi=> by rw [show corto a p i=0 from if_neg (mt (clogs _).mpr hi),Complex.ofReal_zero, zero_smul] -- rw elaboration check
lemma supplyDeck (a : Cover→ℝ) (hw : Width (2*c) C a) (hb : 0≤b) (hd : 0<δ) (hc : 0<c) (hr : 0<n) (ht : 2*n≤B) (hg : Pile b (2*n)*gal δ^n≤ Real.exp (c*n)): Sample δ b c B (fun U=>deck t U a) (fun U=>deck t U (corto a p)) (C*Real.exp (c*n)) p (2*p):=by
  have hh:= hw.mono (show c≤2*c by linarith) le_rfl
  have he:= Width.short a p hh
  have hf : 0≤ C := (tsum_nonneg hh.1).trans hh.2.2
  refine ⟨by positivity,lodge t a hh hb hd hc hr ht hg, lodge t _ he hb hd hc hr ht hg,?_, plea ..⟩
  rw [← lodge_minus t a (corto a p) (hh.unweighted hc.le).2.1 (he.unweighted hc.le).2.1,mul_right_comm, show a - corto a p=(fun i=> if size i ≤ p then 0 else a i) from funext fun i=> by by_cases h:size i ≤ p <;> simp [corto,h]]
  exact lodge t _ (Width.filtered a hw p hc.le) hb hd hc hr ht hg
end YM.QCD.Run
