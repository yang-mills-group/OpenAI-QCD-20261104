import YM.QCD.Acre.Yonder
import YM.QCD.Raft.Roads

/-! # trajectory stations: fixed ratio. period mesh at every rung. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft
open Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {j t k i l n N: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ β b C D H u v x y W:ℝ}{p:ChartRatio su}{M:ℕ→ Bed}{T:ℕ→Towers E.L}
variable (X:Soil K q E σ η Ω M T)
def ratioM (S:Side): SparkMesh → SparkMesh:= fun m=>⟨fun i=>m.n i*S,
  tendsto_atTop_mono (fun i=> Nat.le_mul_of_pos_right _ S.pos) m.cofinal, m.ratio,fun i j he=>by change (m.n _).val*S.val=(m.n _).val*S.val*_; rw [m.factor i j he]; ac_rfl, m.parity⟩
lemma hottest (S:Side) (m:SparkMesh)(i:ℕ): (m.n i).val ≤ ((ratioM S m).n i).val:= Nat.le_mul_of_pos_right _ S.pos
abbrev climbM (P:Patch)(m:SparkMesh)(i:ℕ):SparkMesh:= (ratioM P.L)^[i] m
def footM (E:Patch)(m:SparkMesh)(N i:ℕ): SparkMesh := climbM E m (N-i)
lemma foot_align (m:SparkMesh)(h : i<N): footM E m N i=ratioM E.L (footM E m N (i+1)):=by
  rw [footM,footM,climbM,climbM,show N-i=N-(i+1)+1 by omega,iterate_succ_apply']
lemma foot_tall (m:SparkMesh)(j:ℕ):(m.n j).val≤((footM E m N i).n j).val:=by
  unfold footM climbM; induction (N-i) with
  | zero=> exact le_rfl
  | succ k ih=> rw [iterate_succ_apply']; exact ih.trans (hottest ..)

abbrev reachM (E:Patch)(m:SparkMesh):Prop:=∀ i, GateVolume E.J≤ (m.n i).val
lemma reaches (h:E.Branches K su)(m:SparkMesh) (hm: reachM E m)(i j:ℕ):
    Bid.Larger (G:=su) (act (Pike E i) K m j):=by
  let F:= m.n j; have he:=hm j
  refine ⟨h,?_,lt_of_lt_of_le ?_ he⟩
  · change 100*((E.J+3)*E.L.val+4*E.L.val) ≤ (m.n j).val*E.L.val
    rw [← add_mul, ← mul_assoc]; exact Nat.mul_le_mul_right _ he
  unfold GateVolume; omega

-- avoid relying on fixed N in per-step promises
abbrev groveP (E:Patch)(i:ℕ) (K:KernelChoices)(m:SparkMesh): Armada m.n (high (Pike E i) m) E K:= ⟨fun _=>rfl⟩
section reads
variable {i:ℕ}{R R':PathData su}{p:ChartRatio su}{m: SparkMesh}
structure Grade (V:Place (Pike E i) K m R q u v)(R': PathData su)(M:ℕ→ Bed)(T:ℕ→Towers E.L)(A:ChartRatio su)(α γ b ψ D:ℝ): Prop where
 receipts : |α+su.slopeConstant*Real.log E.L.val|+1 ≤ D
 gaps l : PriceGap (V.forest l) q R γ
 
 foresee i' : Guessed (V.forest i') (installed (act (Pike E i) K m i').ratio (T i).A0) (V.u i')
 turns l : ClassicalMatch (V.forest l) q q R R' (V.u l)
 holds l : FiniteBound (V.forest l) R R' q q α A (V.u l) b ψ 1

-- create payouts
abbrev PreCut (K:KernelChoices)(q:Clip)(j:ℕ)(η σ Ω τ v ψ D:ℝ) (N:ℕ) (F L:Side→ℝ):= Transition su K j η σ Ω q.direct σ Ω q.direct v τ v D τ ψ N F L
abbrev EnjoyCut (M:ℕ→Bed)(q:Clip)(u v Λ:ℝ)(i:ℕ)(R:PathData su):Prop := R.Bounds q u v Λ ∧ Attached (M i) R
lemma sprouts (K:KernelChoices)(q: Clip)(j:ℕ)(hp:q.direct ≤1)(hs:0<σ)(hη:0<η)(hD:1≤Ω):∃ u v D ψ,0 < u ∧ 0 ≤v ∧ 0≤ D ∧ 0<ψ ∧
    (∀ (n:ℝ),0≤ n →(Design.top su q).Bounds q u v n) ∧ ∃ N F L, PreCut K q j η σ Ω u v ψ D N F L:=by
  have hv:=zero_le_one.trans hD
  obtain ⟨v,t,hp',ht,H⟩:= transition_cap su lodging simple K j η σ Ω q.direct σ Ω q.direct hη hs hv q.quadratic_pos.le hs hv q.quadratic_pos.le
  obtain ⟨c,hx,h⟩:= Design.bound_arbitrary q su hp t ht
  obtain ⟨d,ψ,w,X,Y,he,hy,W⟩:= H t (max v c) ht (hp'.trans (le_max_left ..)) (pouring su simple _ _ _ _ _ _ hs hη hv q.quadratic_pos.le ht (hp'.trans (le_max_left ..)))
  exact ⟨_,_,_,_,ht,hx.le.trans (le_max_right ..),he,hy,h _ (le_max_right ..),_,_,_, Transition.preserves W le_rfl (le_max_left ..) le_rfl le_rfl le_rfl le_rfl le_rfl⟩

variable {F L : Side →ℝ}
include X
lemma accompanying (h : PreCut K q E.J η σ Ω u v γ D N F L)(hL: LocalRatio p)(hh:E.Branches K su)(hu:N ≤ E.L.val)(hη:0 < η):∃ c:ℝ,0<c∧∀ i (m:SparkMesh)(R₀:PathData su) (Λ Ω':ℝ),1 ≤ Λ → L E.L ≤Λ → reachM E m →F E.L ≤ Ω' → EnjoyCut M q u v Λ i R₀ →
    ∃ (V:Place (Pike E i) K m R₀ q u v) (α:ℝ)(R':PathData su), EnjoyCut M q u v Λ (i+1) R' ∧ Grade V R' M T p α c Ω' γ D:=by
  obtain ⟨P,hP,H⟩:=(Integrated.stationary_scene (G:=su) E.L E.J K η hη).χ
  refine ⟨P,hP,fun i m R Λ Θ hΛ hz hm hΘ ⟨hR,hM⟩=>?_⟩
  let S:= Pike E i; let g:=act S K m
  let f i':=Classical.choice (Tree.select (g i').ratio E.odd_side)
  have hl := reaches hh m hm i
  have hw j:=H _ _ (g j) rfl rfl rfl (hl j) (f j) _ _ _ _ _ _ _ _ _ _ _ (T i) (X.crosses i _ _ (divides0 S m j)) (X.trace i _) hR hM (X.oath i _) (X.trace (i+1) _)
  choose U hU hu' hv using fun j=> (hw j).2
  let Q: Place (Pike E i) K m R q u v:=⟨f,U,hU,hl,Λ,hR⟩
  have hy i (n): Hull (M i) η σ Ω q n su := ⟨(X.fund i).2.1, (X.fund i).2.2.2.1, fun j=>X.trace i j, fun j=>X.oath i _⟩
  have hh : Scud (groveP E i K m) su q q R f U σ u Ω v Ω η Λ σ Ω η (M i) (M (i+1)) (T i) P:=⟨hl,hy _ _,hy _ _,hM,hR,fun l H=> ((X.pay i).2.2.2 l (H.trans (by have h:=E.order_cut; omega))).1,fun j=>X.crosses i _ _ (divides0 S m j),fun j=> (hw j).1,hU,hu',hv⟩
  obtain ⟨R,α,h₁,h₂,h₃,h₄,h₅,h₆⟩:= h m.n _ E (groveP E i K m) q q _ f U _ _ (T i) Λ η P p rfl hu m.cofinal le_rfl le_rfl hh hΛ hP hL
  refine ⟨Q,α,R,⟨h₃ u v Λ hR.width le_rfl le_rfl hz (by linarith),h₂⟩,h₄,fun j=> (hw j).1,hu',h₅,h₆ Θ γ hΘ le_rfl⟩
end reads
end YM.QCD.Acre
