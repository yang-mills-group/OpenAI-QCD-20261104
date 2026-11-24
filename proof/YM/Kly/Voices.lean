import YM.Kly.Chem
import YM.MassiveBridge.Soars
set_option maxHeartbeats 520000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Bridge.Kly
open Function Set Filter Analysis MeasureTheory Measure UV UV.Free
open OS (Cross)
open Fields (pointMoment distinct gram)
open scoped Topology BigOperators InnerProductSpace NNReal ContDiff ComplexOrder Matrix
variable {F:Fields} {S:F.Kernel} {V:Chamber S timeAxis}(P:Spread V)
variable (H:Steady V) (Y:Fields.Euclidean S)(RA:Angular S) {Q:Sequence}{C:Calibration Q}(E:F.System C){B:Bases F}{M':Momentum F}(U:B.Content C M')
variable (x:F.W)(w:P.algebra→⋆ₐ[ℂ]ℂ)(hx:Continuous w)
local notation "Sα"=>bloom P H w
local notation "t₀"=>timeAxis
open OS.Ground (Panes)
open TopologicalSpace Chamber
variable (R:Panes P.algebra)(ht:R.Shines (dome V) P.algebra.subtype V.omega0)
variable (hE:∀ i:R.X, Fields.Euclidean (bloom P H (R.character i)))
noncomputable abbrev Signad (Qo:Chamber S timeAxis)(i:ℕ→Future F timeAxis):= DenseRange (Finsupp.linearCombination ℂ (fun x=> Qo.GNS.plant (i x)))
include E
noncomputable def futureP (n d:ℕ)(x: CapZone n d t₀ F) : Future F t₀ := ⟨parcels x.val,x.property⟩
lemma riseQ : ∃ f:ℕ→ Future F t₀,∀ (S: Fields.Kernel F),∀ Y: Fields.Euclidean S,∀ Q:Chamber S t₀, Signad Q f:=by
     have h(n d:ℕ):∃ s:Set (CapZone n d t₀ F),s.Countable ∧ Dense s:=by haveI:= E.finite d; exact exists_countable_dense _
     choose B hB hd using h
     let C:=⋃ n: ℕ,⋃ d:ℕ, futureP n d '' B n d; obtain ⟨f,hf⟩:= (show Set.Countable (insert (air t₀) C) from (countable_iUnion fun n=> countable_iUnion fun d=> (hB n d).image _).insert _).exists_eq_range (by exact ⟨_,mem_insert _ _⟩); refine ⟨f,fun S Y Q=>?_⟩
     let M:= LinearMap.range (Finsupp.linearCombination ℂ fun i=> Q.GNS.plant (f i)); change Dense (M : Set Q.H)
     have he : Submodule.span ℂ (range Q.GNS.plant) ≤ M.topologicalClosure:=by
           apply Submodule.span_le.mpr; intro x hx; rw [Q.samples E] at hx; obtain ⟨⟨n,d⟩,hx⟩:= mem_iUnion.mp hx; obtain ⟨z,rfl⟩:=hx; have hm: MapsTo (Q.sample n d) (B n d) (M : Set Q.H):=by
                   intro u hu; have hv: futureP n d u∈range f:= hf ▸ subset_insert (air t₀ (F:=F)) C (mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨d,u,hu,rfl⟩⟩)
                   obtain ⟨i,h⟩:= hv; change Q.GNS.plant (futureP n d u)∈ M; rw [← h]; exact ⟨Finsupp.single i 1,by simp⟩
           haveI:= E.finite d; exact hm.closure (Q.sample_cont Y) (hd n d z)
     intro x; exact closure_minimal he M.isClosed_topologicalClosure (Q.GNS.dense x)
include P E H U ht Y
lemma pickGen (T:R.X→ F.Kernel) (h:∀ k b, Continuous (fun i:R.X=>current (T i) b k)∧(∫ i:R.X,current (T i) b k ∂R.μ)= current S b k)(h7:∀ (i:R.X)(v:Cluster F)(hx:distinct v),pointMoment (T i) v= R.character i (M P _ hx))(he:∀ i,Fields.Euclidean (T i)) : ∀ᵐ i ∂R.μ,∃ W: Reconstruction F,W.Theory (T i):=by
     let Qo(i:R.X):=Classical.choice (Bridge.realization (a:=timeAxis) (he i) (E.reflected _)); obtain ⟨f,hf⟩:= riseQ E
     have hx:= lifts P H Y R ht T h h7 he Qo f (fun i=> hf _ (he i) _)
     exact hx.mono fun i hy=> soars E U (he i) hy
include hE
set_option maxRecDepth 8000 in
set_option maxHeartbeats 840000 in
lemma picks : ∀ᵐ i ∂R.μ, ∃ W: Reconstruction F, W.Theory (bloom P H (R.character i)):=by
     exact pickGen P H Y E U R ht (fun i=>bloom P H (R.character i)) (champ P H Y R ht) (fun i v hv=> bless P H (R.character i) v hv) hE
end YM.Massive.Bridge.Kly
#print axioms YM.Massive.Bridge.Kly.picks
