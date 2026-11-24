import YM.Extra.WILSON_STARTUP.Roll
import YM.Next.STATIONARY.FullPlanned
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Harmonic
import YM.QCD.Simple

/-! # Plowing aperture at one fixed shape family
A and T not chosen via overlay after betas. Roll on every period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Classical
open scoped Topology ContDiff BigOperators
variable {j t k i l n: ℕ}{K:KernelChoices}{q: Clip}{E:Patch}{σ η Ω A γ b C D H u v x y:ℝ}{p:ChartRatio su} -- K costs
-- issue clip side
lemma inserted (h:0<γ):∃ p:Clip,p.direct< γ ∧ p.direct<1:=by
  let z:=min γ 1 /2; have he : 0<z:=by unfold z; positivity
  refine ⟨⟨z,z/32,1,he,by positivity,by linarith,by positivity⟩,?_,?_⟩
  all_goals first | exact lt_of_lt_of_le (half_lt_self (show 0 < min γ 1 from lt_min h one_pos)) (min_le_left ..) | exact lt_of_lt_of_le (half_lt_self (show 0 < min γ 1 from lt_min h one_pos)) (min_le_right ..)

def pump (E:Patch) (t:Train E.J):Flight E.J E.J:=⟨E.L,E.odd_side,E.coarse,E.order_cut,le_rfl,by omega,t⟩
def tile (E:Patch) (i:ℕ):Train E.J:=Nat.rec (motive:=fun _=>Train E.J) (Train.top _) (fun _ t=> (pump E t).land) i
abbrev Pike (E:Patch) (i:ℕ):Flight E.J E.J:=pump E (tile E i)
abbrev depot (E: Patch)(K:KernelChoices)(i:ℕ){c f:Side} (h:f.val=c.val*E.L.val):=Flight.visit (Pike E i) K h
structure Soil (K:KernelChoices)(q:Clip)(E:Patch)(σ η Ω:ℝ) (B:ℕ→ Bed) (S:ℕ→Towers E.L) : Prop where
  top : B 0= Design.bed q
  fund i : (B i).covered σ Ω
  trace i n : Floor (B i) q n η Ω
  oath i n : Sworn (B i) n su
  pay i : (S i).Deep σ Ω (E.J-2)
  orient i : (S i).A0=((Pike E i).duo K.penalty).A0
  cell i : (S i).T=((Pike E i).duo K.penalty).T
  crosses i c f (h : f.val=c.val*E.L.val) : Towers.Diagonal (depot E K i (c:=c) (f:=f) h) (B i) (B (i+1)) (S i)
  mGauge i c f (h : f.val=c.val*E.L.val) : Towers.Roll (depot E K i (c:=c) (f:=f) h) (B i) (B (i+1)) (S i) q q

structure Shaking (K:KernelChoices)(q:Clip)(E:Patch)(σ η Ω:ℝ) (B:ℕ→Bed) (S:ℕ→Towers E.L):Prop where
  bear:∀ i,(B i).covered σ Ω
  top:∀ n,(B 0).diagonal.acts n=1
  trace i n: Floor (B i) q n η Ω
  oath i n : Sworn (B i) n su
  pay i : (S i).Deep σ Ω (E.J-2)
  orient i : (S i).A0=((Pike E i).duo K.penalty).A0
  cell i : (S i).T=((Pike E i).duo K.penalty).T
  crosses i c f (h:f.val=c.val*E.L.val) : Towers.Diagonal (depot E K i (c:=c) (f:=f) h) (B i) (B (i+1)) (S i)
  mGauge i c f (h:f.val=c.val*E.L.val) : Towers.Roll (depot E K i (c:=c) (f:=f) h) (B i) (B (i+1)) (S i) q q

lemma shakes (K:KernelChoices) (j:ℕ)(hj:4≤j):∃ q : Clip,q.direct ≤ 1 ∧ ∃ σ η Ω, 0<σ ∧ 0<η ∧ ∃ N:ℕ,∀ E:Patch,E.J=j→ N≤E.L.val → ∃ B T, Shaking K q E σ η Ω B T:=by
  obtain ⟨Q,l,g,d,h⟩:= pledges K
  obtain ⟨p,hp,hp'⟩:= inserted (h.fit j)
  -- already Funds full not restricted
  obtain ⟨w,Z,e,hw,he,H⟩ := F07.answer (TypeFace 3) (Q.Ω j) (Q.η j) (Q.α j) (Q.eta_pos j) (Q.alpha_pos j)
  obtain ⟨x,y,hx,W⟩:= F08.answer p p K.penalty (Q.Ω j) (Q.α j) (Q.α j) (Q.Ω j) e Z (j-2) K.penalty_pos (Q.alpha_pos j) (Q.alpha_pos j) he
  let u:=min x (Q.α j); let v:= max y (Q.Ω j)
  refine ⟨p,hp'.le,u,Q.η j,v,lt_min hx (Q.alpha_pos _),Q.eta_pos _,d j,fun E hJ ht=>?_⟩
  subst j; choose M hM h1 h2 h3 h4 using fun i=> h.bottom _ hj _ hp.le (tile E i)
  have hQ i := h.hop _ _ (show Mag E.J E.J from ⟨hj,hj,Or.inl rfl⟩) (Pike E i)
  have hf i (c f:Side) := check_bleep K (l E.J) (l E.J) (h.net _) (h.net _) (Pike E i) E.order_cut (M i) (M (i+1)) (hM i) (hM (i+1)) (c:=c) (f:=f)
  have hs i (c f:Side) := YM.Next.Free.diagonal K (l E.J) (l E.J) (h.net _) (h.net _) (Pike E i) E.order_cut (M i) (M (i+1)) (hM i) (hM (i+1)) (c:=c) (f:=f)
  let S i := (Pike E i).rollFunds K.penalty (l E.J) (l E.J)
  let R i : Towers E.L := (Pike E i).duo K.penalty
  choose P hP h5 h6 using fun i => H (S i) (hQ i).2.1 ((hQ i).2.2 ht)
  choose T hT hG using fun i=> W (M i) (M (i+1)) (h1 _) (h1 _) _ (h5 i) E.L E.odd_side (R i) (hQ i).1
  have Hc i := hG i 1 (1 * E.L) rfl
  refine ⟨M,T,fun i=> Change.covered_mono (h1 i) (min_le_right ..) (le_max_right ..),h4 0 rfl,
    fun i n=> Change.floor_mono (h2 _ n) le_rfl (le_max_right ..), fun i n => h3 i n su, fun i=> deep_mono _ (hT i) (min_le_left ..) (le_max_left ..),fun i=> (Hc i).first.symm,fun i=>(Hc i).form.symm,fun i c f h'=>?_, fun i c f h'=>?_⟩
  · obtain ⟨h₁,h₂,h₃⟩:= hs i c f h'
    constructor <;> (first| rw [← (Hc i).first,← (Hc i).form]| rw [← (Hc i).first]| rw [← (Hc i).form]) <;> assumption
  exact F09.answer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hG i _ _ h') (h2 _ f) (h2 _ c) (hs i c f h') (fun n=>(h6 i n).1) (hf i c f h')

lemma sustain (K: KernelChoices) (j:ℕ)(hj:4 ≤j):∃ q:Clip,q.direct ≤ 1 ∧ ∃ σ η Ω,0 < σ ∧ 0 < η ∧ 1 ≤ Ω ∧ ∃ N:ℕ,∀ E:Patch,E.J=j → N ≤ E.L.val → ∃ M T, Soil K q E σ η Ω M T:=by
  obtain ⟨p,hp,s,e,c,hs,hc,n,H⟩:= shakes K j hj
  obtain ⟨u,D,hU,hD⟩:= spin_cost p s c hs
  let v:= min s u; let A:= max (max 1 c) D
  have he : 1 ≤ A:= (le_max_left ..).trans (le_max_left ..); have ht : c ≤ A:= (le_max_right ..).trans (le_max_left ..); have hh := lt_min one_pos hc
  refine ⟨p,hp,v,min 1 e,A,lt_min hs hU,hh,he,n,fun E hs hz=>?_⟩
  obtain ⟨M,T,h⟩:= H E hs hz
  obtain ⟨X,H⟩:= hD _ hp (h.bear 0).2.2.2.1
  obtain ⟨hg,hL⟩:= H _ _ _ (h.pay 0)
  refine ⟨Function.update M 0 (bed p),Function.update T 0 (spin X (T 0)),⟨Function.update_self ..,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i; cases i
    · rw [update_self]; exact Design.covered p hp he
    rw [update_of_ne (by omega)]; exact covered_mono (h.bear _) (min_le_left ..) ht
  · intro i n; cases i
    · rw [update_self]; exact Design.level p hp n (min_le_left ..) he
    rw [update_of_ne (by omega)]; exact floor_mono (h.trace _ _) (min_le_right ..) ht
  · intro i n; cases i
    · rw [update_self]; exact Design.top_sworn p hp
    rw [update_of_ne (by omega)]; exact h.oath _ _
  · intro i; cases i
    · rw [update_self]; exact deep_mono _ hg (min_le_right ..) (le_max_right ..)
    rw [update_of_ne (by omega)]; exact deep_mono _ (h.pay _) (min_le_left ..) ht
  · intro i; cases i
    · rw [update_self]; exact h.orient 0
    rw [update_of_ne (by omega)]; exact h.orient _
  · intro i; cases i
    · rw [update_self]; exact h.cell 0
    rw [update_of_ne (by omega)]; exact h.cell _
  · intro i c f h'; cases i
    · rw [update_of_ne (by omega : 0+1 ≠ 0),update_self,update_self]
      obtain ⟨a,b,c⟩:= top_diagonal (h.crosses 0 c f h') (h.trace 0 f) (h.top f)
      exact ⟨a,b,c⟩
    rw [update_of_ne (by omega),update_of_ne (by omega),update_of_ne (by omega)]; exact h.crosses ..
  intro i c f h'; cases i
  · rw [update_of_ne (by omega : 0+1≠ 0),update_self,update_self]; obtain ⟨h₁,h₂,h₃⟩:= hL c f h'; exact trans_roll (h.mGauge 0 c f h') h₁ h₂ (h₃ _ _ (h.trace 0 f) (h.top f))
  rw [update_of_ne (by omega),update_of_ne (by omega),update_of_ne (by omega)]; exact h.mGauge ..
end YM.QCD.Acre
