import YM.QCD.Eyrie.Cabin

/-! # plog on shell logarithmic weighted jet -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Finset Lat Kit Rudder Metric Quarry Precision
open Push.Uniform YM.Further.PhysicalPeriodLimitF933 Jacobi Tree
open scoped Topology Matrix ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {n c f : Side} {I X : Type} {k m : ℕ} {r a b d C B R A S u:ℝ} {W : RG.StepData c f}

lemma gather_fl {I X : Type} [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X] {F:Positions I→X} {l : I→Site n} {x:Site n}
    (h: ContDiffAt ℝ ω F 0)(ht: 0<r)(he:Beacon l r 2 F x 0 C): Flock l Push.Uniform.bolt F x r C:= by
  have hx:= he 0 (by decide) ![]; simp only [entry,iteratedFDeriv_zero_apply,spanSites, univ_eq_empty, sum_empty, Nat.cast_zero, mul_zero, Real.exp_zero,mul_one] at hx
  refine ⟨ht,(norm_nonneg _).trans hx,h,hx,fun i=>?_,fun i j=>?_⟩
  · have hh:= he 1 (by decide) ![i]; simpa only [Decay, blade,entry,iteratedFDeriv_one_apply,spanSites,Matrix.cons_val_zero, Fin.sum_univ_one] using! hh
  have hh:= he 2 (by decide) ![i,j]; simp only [entry,spanSites, Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.cast_add,mul_add,Real.exp_add] at hh
  rw [iter _ _ h,show ![Push.Uniform.bolt i,Push.Uniform.bolt j]= Push.Uniform.bolt ∘ ![i,j] from funext fun i=> by fin_cases i <;> rfl]; exact hh

variable (H:Forest W.ratio)
def gloss (x : Positions (Push.Uniform.Joint H su)):= Stationary.content (Push.Uniform.fine su H x)
def pier (j:su.ColorIndex)(U:su.Mat):ℝ:=su.plog U j
lemma glosses (z : Positions (Push.Uniform.Joint H su))(x: Site f) (i : Axis)(j : su.ColorIndex):
    gloss (W:=W) H z (x,Exterior.coord i,j)=pier j (su.mat (Push.Uniform.fine su H z (x,i))):=by
  rw [gloss,← Stationary.arm_apply su f 1 (Stationary.content (Push.Uniform.fine su H z)),Stationary.content_at]; rfl
lemma pier_all : ∃ C:ℝ,0≤C ∧ ∀ j, Allows 2 (pier j) 1 C:=by
  have ht j: ContDiffAt ℝ ω (pier j) 1:=(PiLp.proj (p:=2) (𝕜:=ℝ) (fun (_:su.ColorIndex)=>ℝ) j).contDiff.contDiffAt.comp (f:=su.plog) _ su.plog_diff
  choose C H using fun i=> exists_allows (isCompact_singleton (x:=(1:su.Mat))) (fun x hx=> (Set.mem_singleton_iff.mp hx).symm ▸ ht i) 2
  refine ⟨∑ i,C i,sum_nonneg (fun i _=> ((H i).2 1 (Set.mem_singleton 1)).nonneg),fun i=>((H i).2 1 (Set.mem_singleton 1)).mono (single_le_sum (fun i _=> ((H i).2 1 (Set.mem_singleton _)).nonneg) (mem_univ i))⟩
lemma ages : ∃ C:ℝ, 0 ≤ C∧∀ {c f:Side}(W : RG.StepData c f) (H:Forest W.ratio) i, Allows 2 (fun x => gloss H x i) 0 C:=by
  obtain ⟨Z,hZ⟩:= paint_supply su 2
  obtain ⟨u,hu,h⟩:= pier_all
  refine ⟨composeCost 2 u (fineCost su 2 Z),?_,?_⟩
  · have hc:=hZ.1; unfold composeCost fineCost outerCost composeCost; have := shade_pos su; positivity
  intro c f W H i; rcases i with ⟨x,i,j⟩; obtain ⟨i,rfl⟩:= Exterior.axisEquiv.surjective i; have he:=fine_supply H hZ; simp_rw [show Exterior.axisEquiv i=Exterior.coord i from rfl,glosses];
  exact Allows.comp (g:=pier j) (show Allows 2 (pier j) (su.mat (Push.Uniform.fine su H 0 (x,i))) u by rw [he.1]; exact h j) (he.2.2 (x,i) 0 (by simp))
lemma honors (i : Road f): Requests Set.univ (fun x=> gloss H x i) (address H su) (traceG f i) W.ratio.count.val := by
  rcases i with ⟨x,i,j⟩; obtain ⟨i,rfl⟩:= Exterior.axisEquiv.surjective i; intro y _ z _ h; simp_rw [show Exterior.axisEquiv i=Exterior.coord i from rfl,glosses]; rw [fine_read H h (x,i) (by rw [show traceG f _=x from rfl,separation_self,zero_add])]
lemma capsG (L : Side)(hr:0<r) : ∃ D':ℝ,0 ≤ D' ∧∀ {c f : Side} (W : RG.StepData c f) (H:Forest W.ratio), W.ratio.count=L→ ∀ i,
    Flock (address H su) Push.Uniform.bolt (fun x=> gloss H x i) (traceG f i) r D':=by
  obtain ⟨C,hc,H⟩:=ages
  refine ⟨C*Real.exp (r*(↑(2*L.val:ℕ))),mul_nonneg hc (Real.exp_pos _).le,fun {c f} W A ht i=>?_⟩
  refine gather_fl (H W A i).analytic hr ?_; rw [← ht]; exact (H _ _ i).beacon (honors _ _) Filter.univ_mem hr.le
end YM.QCD.Eyrie
