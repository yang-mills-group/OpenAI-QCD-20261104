import YM.QCD.Eyrie.Dart

/-! # Into plog. Recycle native width. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Metric Lattice Wilson Lat Push.Uniform Tree RG Precision
open Quarry Finset YM.Further.PhysicalPeriodLimitF933 Jacobi
open scoped Topology Matrix Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {f c n : Side} {S : StepData c f} {H : Forest S.ratio} {u : Bid.Dir su c→ AxisChart su H} {j l : ℕ} {p : Clip} {B A ε r Λ : ℝ} {K : KernelChoices} {R : PathData su}

def buildU (H : Forest S.ratio) (u: Bid.Dir su c →AxisChart su H): Cnr c → Positions (Push.Uniform.Joint H su):= curve (Push.Uniform.station u) ∘ (mergeC c).symm
lemma build0 (h: Critical H p R u): buildU H u 0=0:=by
  have hu : Push.Uniform.station u 0=0:=by unfold Push.Uniform.station; simp [h.1]
  unfold buildU curve; rw [Function.comp_apply,map_zero,hu]; exact (partSpace _ _).symm.map_zero
lemma modelU (H:Forest S.ratio) (u: Bid.Dir su c→ AxisChart su H) (x): fine su H (buildU H u x)=(Stationary.encamp H u x).1:=by
  unfold fine buildU curve; rw [Function.comp_apply]; unfold Push.Uniform.outer; rw [paint_meet (S:=S)]; unfold Push.Uniform.station; simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  have hf : tint su _ ((mergeC c).symm x)=Stationary.arm su c 1 x := by simp [mergeC]
  rw [hf]; rfl

def journal (H : Forest S.ratio)(u: Bid.Dir su c→ AxisChart su H): Cnr c→Cnr f:= gloss H ∘ buildU H u
lemma journalC (H : Forest S.ratio)(u: Bid.Dir su c→AxisChart su H)(x) : journal H u x= Stationary.content (Stationary.encamp H u x).1:=by unfold journal gloss; rw [Function.comp_apply,modelU]
lemma journal_nil (h:Critical H p R u):journal H u 0=0:= by rw [journalC, Stationary.encamp_zero h]; exact Stationary.content_one
lemma journal_return (h:Critical H p R u): ∀ᶠ x in 𝓝 0,(Stationary.encamp H u x).1= Stationary.input su f (journal H u x):=by
  let B x := (Stationary.encamp H u x).1; have he : Tendsto B (𝓝 0) (𝓝 1):=by
    have ht : B 0=1:=by unfold B; rw [Stationary.encamp_zero h]; rfl
    exact ht ▸ ((Stationary.camp_thaw h).cont.fst).tendsto
  filter_upwards [he.eventually Stationary.content_encodes] with x ht; rw [journalC]; exact ht.symm

lemma marquee (W : Before su ε A j K l) (P : Patch)(p : Clip) : ∃ r D:ℝ, 0<r ∧ 0<D ∧ ∀ {C F:Side}(S : StepData C F), S.patch=P → P.J=j → S.kernel=K → Bid.Larger (G:=su) S → ∀ (H:Forest S.ratio) (u:Bid.Dir su C→AxisChart su H) (R: PathData su)(Λ:ℝ), W.Service H p R u → R.Bounds p ε A Λ → ∀ i,
    Flock (beam S.ratio) Push.Uniform.bolt (fun x=>journal H u x i) i.1 r D:=by
  let T:= W.tables p P
  let s:=responseRate T.coords l T.value T.width T.gap
  let d:=curveCost T.coords T.value T.width T.gap 2
  by_cases Hv : 0<s∧0<d
  · obtain ⟨a,ha,H⟩:=capsG P.L (show 0<3*s by have :=Hv.1; positivity)
    have he := intakeQ_nn (ν:=townCost su) Hv.1 Hv.2.le
    refine ⟨s,1+a*intakeQ s d (townCost su),Hv.1,add_pos_of_pos_of_nonneg one_pos (mul_nonneg ha (zero_le_one.trans he)),fun {c f} S ht hj hS hK F u R Λ hu hv i=>?_⟩
    have h (i:Push.Uniform.Joint F su): Flock (beam S.ratio) Push.Uniform.bolt (fun x=>buildU F u x i) (address F su i) s d:= by
      have hp:= (glints hu hv hK (ht ▸ hj) hS i).2.2
      rw [ht] at hp; exact hp
    have hp:=H S F (show S.ratio.count=P.L from congr_arg Patch.L ht) i
    have hi:= migrate (town F) hp (build0 hu.critical) (contDiffAt_pi.mpr fun i=> (h i).host) Hv.1 Hv.2.le h le_rfl
    exact hi.patron (le_add_of_nonneg_left zero_le_one)
  refine ⟨1,1,zero_lt_one,zero_lt_one,fun {c f} S ht hj hS hK F u R Λ hu hv i=>?_⟩
  rcases i with ⟨x,i',j⟩
  let z : Push.Uniform.Joint F su := .inl (((0,i'),j))
  obtain ⟨hz,hv,-⟩:= glints hu hv hK (ht ▸ hj) hS z; rw [ht] at hz hv; exact False.elim (Hv ⟨hz,hv⟩)
lemma multIF {I:Type}[Fintype I] (n:Side) : Multiplicity (fun i:Site n×I=>i.1) (Fintype.card I):=by
  intro x; apply le_trans (card_le_card_of_injOn (α:=Site n × I) (s:=univ.filter _) (t:=univ) Prod.snd (fun i _=> mem_univ _) ?_) (card_univ.le)
  rintro i hi j hj hz
  exact Prod.ext ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm) hz
lemma multIJ {I:Type}[Fintype I] (ρ:Ratio c f):Multiplicity (fun i:Site c × I => ρ.embed i.1) (Fintype.card I):=(multIF (I:=I) f).comp (f:=fun i:Site c × I=> (ρ.embed i.1,i.2)) (fun i j h=> Prod.ext (ρ.embed_injective (congr_arg Prod.fst h)) (congr_arg (fun k:Site f×I=>k.2) h))
lemma tally (n:Side):Multiplicity (traceG n) (townCost su):=by
  intro x; have ht:= multIF (I:=Exterior.TypeFace 1 × su.ColorIndex) n x; exact ht.trans (Nat.le_add_right ..)
end YM.QCD.Eyrie
