import YM.Elms.Shake
/-! # Actually average over root for all rank pivots, obtaining gauge invariants.
Memo includes projected cutoff supplies.D.Y
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker ComplexOrder
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Civic
open QCD.Kites Poised.Beacon PrismD
local notation "τ"=> su.probHaar
open scoped LoomC
noncomputable local instance realM(d:ℕ): NormedSpace ℝ (Mini d):= NormedSpace.restrictScalars ℝ ℂ _
abbrev Banner := (n:Side) × Cover × Grid n × Finset (Pairs (Modes n 6))
def barTap (i:Banner): Drape →ₗ[ℂ] ℂ:= coef i.2.2.2 ∘ₗ exposeD _ i.2.1 i.2.2.1
lemma anyPay(x:Drape): Integrable (fun u=> exposeD n o U (whereby u x)) τ:= (factual U o x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma bar_band(x:Drape)(i:Banner): Continuous (fun u=> barTap i (whereby u x)) := (coef i.2.2.2).continuous_of_finiteDimensional.comp (factual i.2.2.1 i.2.1 x)
lemma bar_blank(x:Drape)(h:∀ i,barTap i x=0): x=0:=by
    funext n o; apply ContinuousMap.ext; intro U; let Y:=exposeD n o U x; rw [pointwiseE U o x]; change Y=0; rw [←write Y]; simp_rw [show ∀ i:Finset (Pairs (Modes n 6)),coef i Y=0 from fun i=> h ⟨n,o,U,i⟩, zero_smul, sum_const_zero]
def Shears (X Y:Drape):Prop:= ∀ n o U, exposeD n o U Y = ∫ u:su.El, exposeD n o U (whereby u X) ∂τ
variable {X Y:Drape} {g s:ℕ}
lemma shed (h:∀ i:Banner,barTap i Y=∫ u,barTap i (whereby u X)∂τ):Shears X Y:=by
   intro n o U; apply (Grass.blades _).repr.injective; ext1 i; change Grass.coef i _=Grass.coef i _; let L:=(Grass.coef i).toContinuousLinearMap; have ht:= L.integral_comp_comm (anyPay U o X); exact (h ⟨n,o,U,i⟩).trans ht
lemma Shears.unique {Z:Drape}(h:Shears X Y)(he:Shears X Z):Y=Z:=funext fun n=>funext fun o=>ContinuousMap.ext (fun U=>(h n o U).trans (he n o U).symm)
lemma sheen (h:Fins X): ∃ y:Drape,y∈OrbitW X ∧ Shears X y:=by
     haveI:Module.Finite ℂ (OrbitW X):= Module.Finite.of_fg h; obtain ⟨y,hy,hp⟩:= finite_cash (fun u=>outsideA X u) barTap bar_blank (bar_band X); exact ⟨y,hy,shed hp⟩
lemma Shears.in_spin (h:Shears X Y)(hh:Fins X): Y ∈ OrbitW X:=by obtain ⟨z,hz,he⟩:=sheen hh; rw [h.unique he]; exact hz
lemma Shears.entitled (h:Shears X Y)(hh:Writing X g s): Draft Y g s:=by
   refine Submodule.span_induction (p:=fun y _=>Draft y g s) ?_ (drought g s) (fun y z _ _ hy hz=> Draft.joins hy hz) (fun i z _ hz=> Draft.scale hz i) (h.in_spin hh.film); rintro _ ⟨u,rfl⟩; exact hh.draws u
lemma Shears.stamped (h:Shears X Y)(u:su.El): whereby u Y=Y:=by
   funext n o; apply ContinuousMap.ext; intro U; let V:= Lattice.gauge (gways u n) U; let L:=(slots 6 (gways u n)).toLinearMap.toContinuousLinearMap; change L (exposeD n o V Y) = Y n o U; rw [h, ← L.integral_comp_comm (anyPay ..)]; have he(p): L (exposeD n o V (whereby p X))= exposeD n o U (whereby (p*u) X):=by rw [← twiceR]; rfl
   simp_rw [he]; rw [integral_mul_right_eq_self (fun u=>exposeD n o U (whereby u X)),← h]; rfl
lemma Shears.gauged (h: Shears X Y) (hh:Fins X)(he:Roots X): ∀ n o, Lat.Invariant (Y n o):=by
   have hx: Y∈grooming:=Submodule.span_le.mpr (show Set.range (fun u:su.El=>whereby u X) ⊆ ↑grooming from fun _ ⟨v,hv⟩=> hv ▸ tintedR X v he) (h.in_spin hh)
   intro n o k; rw [show Roots Y from hx, h.stamped _] -- show?
lemma Shears.smul (h:Shears X Y)(c:ℂ): Shears (c • X) (c • Y):= by intro n o U; simp_rw [map_smul,integral_smul,h n o U]
lemma Shears.add {p q:Drape}(h:Shears X Y)(hh:Shears p q):Shears (X+p) (Y+q):=by intro n o U; simp_rw [map_add,h n o U,hh n o U]; rw [integral_add (anyPay ..) (anyPay ..)]
-- translation.Renderings: projection on same average symbol using graph of all tests. Avoid real dynamic topology on module. enough for any formula.X
noncomputable def tinted (d:ℕ)(u:su.El)(p:Mini d):= LoomC.tint u d p
lemma travelsZ(H:SourceRead.TaperHol)(p:Mini d)(u:su.El)(h:TravelsP H X p): TravelsP H (whereby u X) (tinted d u p):=by
    obtain ⟨M,h⟩:=h; exact ⟨M, fun n o hn=> Poised.Beacon.coloredO H o u (X n o) p.val (h n o hn)⟩ -- transformed.C ledger
lemma travelsPlus (H:SourceRead.TaperHol)(p q:Mini d)(h:TravelsP H X p)(hv:TravelsP H Y q) : TravelsP H (X+Y) (p+q):=by obtain ⟨M,hm⟩:=h; obtain ⟨N,hv⟩:=hv; exact ⟨N+M,fun n o hn=> plusA o H (X n o) (Y n o) p q (hm n o (by omega)) (hv n o (by omega))⟩
lemma travels_bill (H:SourceRead.TaperHol)(p:Mini d)(h:TravelsP H X p)(t:ℂ): TravelsP H (t • X) (t • p):=by obtain ⟨M,hm⟩:=h; exact ⟨M,fun n o h=>constA o H t _ _ (hm n o h)⟩
lemma Shears.paid (H: SourceRead.TaperHol)(p:Mini d)(h:Shears X Y)(he:Fins X)(hp:TravelsP H X p) : TravelsP H Y (colorRing d p):=by
     let P(u:su.El):= (whereby u X,tinted d u p); let S:= Submodule.span ℂ (Set.range P); let B:= Module.finBasis ℂ (Mini d)
     letI: Module.Finite ℂ S:= by
        let T:=(OrbitW X).prod (⊤:Submodule ℂ (Mini d)); haveI:Module.Finite ℂ T := Module.Finite.of_fg (Submodule.FG.prod he (Module.Finite.fg_top (R:=ℂ) (M:=Mini d))) -- he is Fins
        have hg:S ≤ T:=Submodule.span_le.mpr (fun x ⟨u,h⟩=> h ▸ ⟨outsideA X u,Submodule.mem_top⟩); exact FiniteDimensional.of_injective (Submodule.inclusion hg) (Submodule.inclusion_injective hg)
     let f:=Sum.elim (fun b:Banner=> barTap b ∘ₗ LinearMap.fst ℂ Drape (Mini d)) (fun i:Fin (Module.finrank ℂ (Mini d))=> B.coord i ∘ₗ LinearMap.snd ℂ Drape (Mini d)); have he(u):P u∈S:=Submodule.subset_span ⟨u,rfl⟩
     have hv(x:Drape × Mini d)(h:∀ i,f i x=0):x=0:=by
        refine Prod.ext (bar_blank _ (fun i=>h (.inl i))) ?_; apply B.equivFun.injective; funext i; rw [show (0:Drape × Mini d).2=0 from rfl,map_zero]; exact h (.inr i)
     have hf(i): Continuous (fun u:su.El=> f i (P u)):=by rcases i with i|i; exact bar_band X i; exact (B.coord i).continuous_of_finiteDimensional.comp (circulation p)
     obtain ⟨x,hx,hP⟩:= @finite_cash _ _ _ _ P S _ he f hv hf
     have hx' : Shears X x.1:=shed (fun i=>hP (.inl i)); rw [h.unique hx']
     have ht : x.2=colorRing d p:=by
         apply B.equivFun.injective; funext i; let L:=(B.coord i).toContinuousLinearMap; exact (hP (.inr i)).trans (L.integral_comp_comm (tax p))
     rw [←ht]; refine Submodule.span_induction (p:=fun i _=> TravelsP H i.1 i.2) ?_ ?_ (fun a b _ _ h1 h2=> travelsPlus H _ _ h1 h2) (fun a b _ h1=> travels_bill H _ h1 a) hx
     · rintro _ ⟨e,rfl⟩; exact travelsZ H p e hp
     have h:= travels_bill H _ hp 0; rw [zero_smul,zero_smul] at h; exact h
-- Haar lore commutes
lemma prismR (p:Mini d)(t v:ℝ): prism t v d (colorRing d p)= colorRing d (prism t v d p):=by
    let L:=(prism t v d).toContinuousLinearMap; change L (∫ u:su.El, tint u d p ∂su.probHaar)=_; rw [← L.integral_comp_comm (tax _)];
    simp_rw [show ∀ u:su.El, L (tint u d p)=tint u d (prism t v d p) from fun u=> Subtype.ext (by change (prism t v d _).val=colorAct u (prism t v d p).val; rw [measures, measures]; exact (colorWidth t v u p.val).symm)]; rfl
lemma Shears.survey {H:SourceRead.TaperHol}{p:Mini d}(h:Shears X Y)(he:Writing X g s)(hp: Survey H X g s p): Survey H Y g s (colorRing d p):=by
    obtain ⟨z,hz,hr⟩:=hp.grantX; refine ⟨h.entitled he,colorRing d z,h.paid H z he.film hz,?_⟩; have hf:= ((colorRing d).continuous_of_finiteDimensional.tendsto p).comp hr; refine hf.congr' (Eventually.of_forall fun i=>?_); simp only [prismR, Function.comp_apply, map_smul] -- args
end Civic
end Arbor
end SparK
end YM.Massive.Elm
