import YM.Gust.Maple
set_option maxHeartbeats 540000
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Gust
open Function Set Filter Analysis Tarn Tarn.Choir QCD QCD.Lat QCD.Grass Wilson UV
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Matrix Classical
variable {C:Sequence}{P:Calibration C}{K:Choir}{d m n:ℕ}{T:Pollens P K}(hK:K.Domestic)
local notation "J"=>Fin (n+1)
local notation "Ix"=>Kind n
local notation "Ω"=> lampU P K
namespace Mater
variable {s:Signed}{p:EuPin}(h:p.Lifts s) (a:Axis)
variable (hf:Foil P K T)
include hf
lemma coinP : Ω ∈ Col T false:=by
       rw [hue,← hf.unit 0 none,T.p,show tauMod false=1 from rfl,one_smul]; apply congr_arg; apply Subtype.ext; rw [RawSym.parityActs,P.sym.unitActs]; change parityAct (unit _)=unit _; unfold parityAct UV.unit; rw [TensorProduct.map_tmul]; simp only[LinearMap.id_coe, id_eq,AlgHom.toLinearMap_apply,map_one]
lemma coinL(a:Axis) : T.adj a Ω=Ω:=by
       rw [← hf.unit 0 none,T.a]; apply congr_arg; apply Subtype.ext; rw [RawSym.adjActs,P.sym.unitActs]; change UV.adj _ (UV.unit _)= UV.unit _; unfold UV.adj UV.unit; rw[TensorProduct.map_tmul,LinearMap.comp_apply,LinearMap.comp_apply,show conjGPol 1=1 from map_one (MvPolynomial.map (starRingEnd ℂ)),dagger_one]; simp only [AlgHom.toLinearMap_apply,map_one]
omit hf
noncomputable def relic (hf:Foil P K T)(n:ℕ):Mater T n:=⟨none,fun _=>Ω,fun i=>by induction i using Fin.cases <;> exact coinP hf⟩
-- Grain at basis.S.Size.
variable (n)
abbrev liveS (b:Bool)(d:ℕ):= Col T b ⊓ K.level (2*d)
local notation "Λ"=> Fin (n+1)
variable {n}
noncomputable def signsB (b:Bool)(d:ℕ): Module.Basis (Fin (Module.finrank ℂ ↥(liveS (T:=T) b d))) ℂ ↥(liveS (T:=T) b d):=by
        letI:FiniteDimensional ℂ ↥(liveS (T:=T) b d):=FiniteDimensional.of_injective (Submodule.inclusion (show liveS (T:=T) b d ≤ K.level (2*d) from inf_le_right)) (Submodule.inclusion_injective _); exact Module.finBasis ..
-- each ticket
noncomputable abbrev textP (T:Pollens P K) (x:Ix)(d:ℕ):=(i:Fin (n+1))→ Fin (Module.finrank ℂ (liveS (T:=T) (Kind.q x i) d))
noncomputable abbrev ScriptP (T:Pollens P K)(d n:ℕ):= Σ x:Kind n,textP T x d
instance : Fintype (ScriptP T d n):= inferInstanceAs (Fintype ((x:Kind n)× textP T x d))
noncomputable def givenP(x:ScriptP T d n):Mater T n:= let G j:= signsB (T:=T) (Kind.q x.1 j) d (x.2 j); ⟨x.1,fun i=> (G i).val,fun i=>(G i).property.1⟩
abbrev Stay (x:Mater T n)(d:ℕ):=∀ i,x.v i∈K.level (2*d)
lemma started(x:ScriptP T d n):Stay (givenP x) d:=fun i=> (signsB (T:=T) _ d (x.2 i)).property.2
include hf in
lemma stay_one: Stay (relic hf n) d:=by
       rintro x; change Ω∈ _; exact ⟨_,hf.unit _ none ⟩
variable (x:Mater T n)(hl:Stay x d)
include hl
lemma gloss :∃ c:textP T x.u d →ℂ, Fees (plant x) (∑ j:textP T x.u d,c j • plant (givenP ⟨x.u,j⟩ (d:=d))):=by
     let E(i:J):= signsB (T:=T) (Kind.q x.u i) d; let l(i:J): ↥(liveS (T:=T) (Kind.q x.u i) d):= ⟨x.v i,x.mem i,hl i⟩
     let c(i:J):= (E i).repr (l i); let a(i:J):= fun j=> (E i) j; let N(i:J): Finset (Fin (Module.finrank ℂ (liveS (T:=T) (Kind.q x.u i) d))):= Finset.univ
     have hv:x.v=(fun i=>∑ j∈N i,(c i j) • ((a i j).val)):=by funext i; exact (by have h: (l i)=∑ j∈N i,(c i j) • a i j:= ((E i).sum_repr _).symm; change (l i).val=_; rw [h,Submodule.coe_sum]; rfl)
     refine ⟨fun j=> ∏ i,c i (j i),fun M=>?_⟩
     rw[map_sum,once,hv]; simp_rw [map_smul,once]
     -- map_sum_finset RHS over Finset.pi. convert
     have he:=(M x.u).map_sum (fun i j => c i j • ((a i j).val)); simp only[MultilinearMap.map_smul_univ] at he; refine he.trans ?_; refine Finset.sum_congr ?_ ?_; · rfl
     intro j _; rfl
omit hl
include h hf
lemma coinσ : T.spin p Ω=Ω:=by
       rw [←hf.unit 0 none,T.w p s h]; apply congr_arg (K.focus none _); apply Subtype.ext; rw [RawSym.pinActs,P.sym.unitActs]; unfold pinAct UV.unit; rw[TensorProduct.map_tmul]; simp only[AlgHom.toLinearMap_apply,map_one]
omit h hf
include h hl
lemma staying : Stay (act hK h x) d:=by
        intro j; obtain ⟨y,hx⟩:=hl j; change T.spin p (x.v j)∈_; rw [←hx,T.w _ _ h]; exact ⟨_,rfl⟩
omit h
lemma pigment : Stay (eye hK a x) d:=by
      intro i; change T.spin _ (T.adj a _) ∈_; obtain ⟨p,h⟩:=hl i; rw [←h,T.a,T.w _ _ (couture a)]; exact ⟨_,rfl⟩
-- support submodule of stay
omit hl
abbrev Binds (T:Pollens P K) (d n:ℕ):Submodule ℂ (Stake T n):= Submodule.span ℂ (plant '' {x | Stay x d}) -- d shadow
lemma enter(h:Stay x d): plant x∈ Binds T d n:= Submodule.subset_span ⟨_,h,rfl⟩
end Mater
end YM.Massive.Gust
#print axioms YM.Massive.Gust.Mater.gloss
