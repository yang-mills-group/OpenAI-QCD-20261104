import YM.Massive.Stratum.Oolitic

/-!
# Pre-stride column stage prices, raising order

Use `Stage i` in derivative orders yet to be determined; shape index at label `i`
is `i+4` with witness obtained *before* any `Flight` realization or lower bounds on `L`.
For cut, terminal startup is required on a pair with same Stage (arrange schedule).
Modify `Acre.Stratum.Oolitic` proofs; not directly use constant-J path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum.MarchQ
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Classical
open scoped Topology ContDiff BigOperators

variable {i j k h n t :ℕ}{K: KernelChoices} {p q:Clip} {σ η Ω:ℝ}
-- stage indices in ℕ. Use Ser for type of high/low pair, with adjacency.
abbrev rank (i:ℕ):ℕ:= i+4
theorem rank_ge (i:ℕ):4≤ rank i :=by unfold rank; omega
structure ChangeQ where
  lo:ℕ
  -- high fine index = up
  hi:ℕ
  path : hi=lo ∨ hi=lo+1
  deriving DecidableEq
namespace ChangeQ


abbrev old (b:ChangeQ):ℕ:=rank b.hi
abbrev new (b:ChangeQ):ℕ:=rank b.lo
abbrev steady (i:ℕ):ChangeQ:= ⟨i,i,Or.inl rfl⟩
abbrev enter (i:ℕ):ChangeQ:= ⟨i,i+1,Or.inr rfl⟩
lemma shape (b:ChangeQ): Mag b.old b.new:= ⟨rank_ge _,rank_ge _,by
     have h:=b.path; unfold old new rank; omega⟩
end ChangeQ
open ChangeQ
structure DeltaW (K:KernelChoices)(p q:Clip)(σ Ω:ℝ)(S:Flight j k)(B T:Bed)(V:Towers S.L):Prop where
   pay : V.Deep σ Ω (j-2)
   orient : V.A0=(S.duo K.penalty).A0
   cell : V.T=(S.duo K.penalty).T
   crosses {c f:Side} (h:f.val=c.val*S.L.val): Towers.Diagonal (S.visit K h) B T V
   mGauge {c f:Side} (h:f.val=c.val*S.L.val): Towers.Roll (S.visit K h) B T V p q
structure Retail (K:KernelChoices)(X:ChangeQ)(P:ℕ→Clip)(Y:(i:ℕ)→Train (rank i)→Bed)(σ η Ω:ℝ)(n:ℕ): Prop where
  pos:0<σ
  growth:0<η
  ample:1 ≤ Ω
  upper i:QuarryQ (P X.hi) σ η Ω (Y X.hi i)
  lower i:QuarryQ (P X.lo) σ η Ω (Y X.lo i)
  edges (S:Flight X.old X.new):n ≤ S.L.val→∃ U, DeltaW K (P X.hi) (P X.lo) σ Ω S (Y X.hi S.wing) (Y X.lo S.land) U
-- Additional same pair receipts for switching high to cutoff.
structure Crown (K:KernelChoices)(i:ℕ)(p: Clip)(Y:Train (rank i)→Bed)(σ η Ω:ℝ)(n:ℕ):Prop where
   top : QuarryQ p σ η Ω (Design.bed p)
   begins : ∀ S:Flight (rank i) (rank i), n≤ S.L.val→ S.wing = Train.top _→ ∃ U, DeltaW K p p σ Ω S (Design.bed p) (Y S.land) U
lemma grow {B:Bed}(h:QuarryQ p σ η Ω B) {s e A:ℝ}(ht:s ≤ σ)(he:e≤η)(hA:Ω ≤ A): QuarryQ p s e A B:=⟨covered_mono h.fund ht hA,fun n=>floor_mono (h.trace n) he hA,h.oath⟩
lemma crowned (b:ℕ){P:ℕ→Clip}{Y:(i:ℕ)→Train (rank i)→Bed}(hp:(P b).direct ≤1)(H:Retail K (steady b) P Y σ η Ω n)(h:∀ c,(Y b (.top (rank b))).diagonal.acts c=1):
    ∃ σ' η' Ω', Retail K (steady b) P Y σ' η' Ω' n ∧ Crown K b (P b) (Y b) σ' η' Ω' n:=by
   obtain ⟨u,D,hU,hD⟩:= spin_cost (P b) σ Ω H.pos
   let v:= min σ u; let A:= max Ω D
   have he : 1 ≤ A:= H.ample.trans (le_max_left ..); have ht : Ω ≤ A:= le_max_left ..; have hh := lt_min one_pos H.growth
   have hs(X:Flight (steady b).old (steady b).new) (hx:n ≤ X.L.val):∃ U,DeltaW K (P (steady b).hi) (P (steady b).lo) v A X (Y _ X.wing) (Y _ X.land) U:=by
       obtain ⟨U,h₀⟩:=H.edges X hx; exact ⟨U, deep_mono _ h₀.pay (min_le_left ..) ht, h₀.orient,h₀.cell,h₀.crosses,h₀.mGauge⟩
   refine ⟨v,min 1 η,A,⟨lt_min H.pos hU,hh,he,fun y=>grow (H.upper y) (min_le_left ..) (min_le_right ..) ht,fun y=>grow (H.lower y) (min_le_left ..) (min_le_right ..) ht,hs⟩,
      ⟨Design.covered (P b) hp he,fun c=> Design.level (P b) hp c (min_le_left ..) he,fun _=> Design.top_sworn _ hp⟩,?_⟩
   intro S hp' hl; obtain ⟨T,hT⟩:= H.edges S hp'
   have h (c:Side): (Y b S.wing).diagonal.acts c=1:=by rw [hl]; exact h c
   have hc: QuarryQ (P b) σ η Ω (Y b S.wing):= H.upper _
   obtain ⟨V,H⟩:= hD _ hp hc.fund.2.2.2.1
   obtain ⟨hg,hL⟩:= H _ _ _ hT.pay
   refine ⟨spin V T,deep_mono _ hg (min_le_right ..) (le_max_right ..), hT.orient,hT.cell,fun {c f} he=>?_,fun {c f} he=>?_⟩
   · obtain ⟨a,b,c⟩:= top_diagonal (hT.crosses he) (hc.trace f) (h f); exact ⟨a,b,c⟩
   obtain ⟨h₁,h₂,h₃⟩:= hL c f he; exact trans_roll (hT.mGauge he) h₁ h₂ (h₃ _ _ (hc.trace f) (h f))

theorem coalition (K:KernelChoices) : ∃ (P:ℕ→Clip)(Y : (i:ℕ)→Train (rank i)→Bed)(σ η Ω:ChangeQ→ℝ)(n:ChangeQ→ℕ),
    (∀ b,Retail K b P Y (σ b) (η b) (Ω b) (n b))∧(∀ i,Crown K i (P i) (Y i) (σ (steady i)) (η (steady i)) (Ω (steady i)) (n (steady i))) ∧ ∀ i,(P i).direct ≤ 1:=by
  obtain ⟨Q,l,g,d,h⟩:= pledges K
  choose P hP hp' using fun i=> inserted (h.fit (rank i))
  have hJ i:(P i).direct ≤1:=(hp' i).le
  choose M hM h1 h2 h3 h4 using fun i j=> h.bottom _ (rank_ge i) (P i) (hP i).le j
  have hi(b: ChangeQ):∃ (u v w:ℝ)(n:ℕ),Retail K b P M u v w n:=by
    let i:=b.old; let s:=min (Q.α i) (Q.α b.new); let C:=max 1 (max (Q.Ω i) (Q.Ω b.new)); let e₀:=min (Q.η i) (Q.η b.new)
    have hs:0<s:=lt_min (Q.alpha_pos _) (Q.alpha_pos _)
    have he:0<e₀:=lt_min (Q.eta_pos _) (Q.eta_pos _)
    have hc:1≤C:=le_max_left ..
    have h' v: QuarryQ (P b.hi) s e₀ C (M b.hi v):=grow (⟨h1 _ _,h2 _ _,fun n=>h3 _ _ n su⟩: QuarryQ _ (Q.α i) (Q.η i) (Q.Ω i) _) (min_le_left ..) (min_le_left ..) ((le_max_left ..).trans (le_max_right ..))
    have h'' v: QuarryQ (P b.lo) s e₀ C (M b.lo v):=grow (⟨h1 _ _,h2 _ _,fun n=>h3 _ _ n su⟩: QuarryQ _ (Q.α b.new) (Q.η b.new) (Q.Ω b.new) _) (min_le_right ..) (min_le_right ..) ((le_max_right ..).trans (le_max_right ..))
    obtain ⟨w,Z,e,hw,he',H⟩:= F07.answer (TypeFace 3) C e₀ s he hs
    obtain ⟨x,y,hx,W⟩:= F08.answer (P b.hi) (P b.lo) K.penalty C s s C e Z (i-2) K.penalty_pos hs hs he' -- check order
    let u:=min x s; let v:=max y C
    refine ⟨u,e₀,v,d i, lt_min hx hs,he,hc.trans (le_max_right ..),fun v=> grow (h' _) (min_le_right ..) le_rfl (le_max_right ..), fun v=> grow (h'' _) (min_le_right ..) le_rfl (le_max_right ..), fun S ht=> ?_⟩
    let A:=S.wing; let B:=S.land
    have hQ := ((h.hop b.old b.new b.shape).revise (σ':=s) (η':=e₀) (min_le_left _ _) (min_le_left _ _) (show Q.Ω i ≤ C from (le_max_left ..).trans (le_max_right ..)) le_rfl) S
    have hf (c f:Side) := check_bleep K (l b.new) (l i) (h.net _) (h.net _) S (rank_ge b.lo) (M b.hi A) (M b.lo B) (hM ..) (hM ..) (c:=c) (f:=f)
    have hh (c f:Side) := YM.Next.Free.diagonal K (l b.new) (l i) (h.net _) (h.net _) S (rank_ge b.lo) (M b.hi A) (M b.lo B) (hM ..) (hM ..) (c:=c) (f:=f)
    let R:=S.rollFunds K.penalty (l i) (l b.new); let T:=S.duo K.penalty
    obtain ⟨p,hP,h5,h6⟩:= H R hQ.2.1 (hQ.2.2 ht)
    obtain ⟨V,hT,hG⟩:= W _ _ (h' A).fund (h'' B).fund p h5 S.L S.odd T hQ.1
    have Hc:=hG 1 (1 * S.L) rfl
    refine ⟨V,deep_mono _ hT (min_le_left ..) (le_max_left ..),Hc.first.symm,Hc.form.symm,fun {c f} h'=>?_,fun {c f} hM'=>?_⟩
    · obtain ⟨h₁,h₂,h₃⟩:= hh c f h'
      constructor <;> (first| rw [← Hc.first,← Hc.form]| rw [← Hc.first]| rw [← Hc.form]) <;> assumption
    exact F09.answer _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hG _ _ hM') ((h' A).trace f) ((h'' B).trace c) (hh c f hM') (fun n=> (h6 n).1) (hf c f hM')
  choose s a u k he using hi
  choose s' a' u' hx ht using fun i=> crowned i (hJ i) (he (steady i)) (h4 i (Train.top (rank i)) rfl)
  refine ⟨P,M,fun b=>if b=steady b.lo then s' b.lo else s b,fun b=> if b=steady b.lo then a' b.lo else a b,fun b=>if b=steady b.lo then u' b.lo else u b,k,fun b=>?_,fun i=>by simpa using ht i,hJ⟩
  dsimp only
  split_ifs with h
  · rw [h]; exact hx _
  exact he b
#print axioms coalition
end YM.QCD.Acre.Stratum.MarchQ
