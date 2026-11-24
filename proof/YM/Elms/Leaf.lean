import YM.Push.RELAY_MARK.Powered
import YM.Elms.Rotor
import YM.Elms.Plasma
/-! # Immutable (units before bare parameters chosen) support/germ tariff for scale-free words. At every coverage. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
-- don't open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
abbrev Drape:= (n:Side) → Cover→Insertion n 6
abbrev Stenc:= Finset Cover
-- realized, MAKE point literals; no zero overlap assumption in these semantics.
def grant (S:Stenc)(D: Cylinder.Formula S 6) : Drape:=fun n o=>Temper.Realize.placed S n o D
lemma granting (S:Stenc)(D:Cylinder.Formula S 6) : grant S D n o U=tongue S o (porch S (expandAt (wrap n o) U) D):=rfl
structure Book (S:Stenc)(X:Drape)(g s:ℕ) : Prop where
    funded: ∃ F: Cylinder.Formula S 6, grant S F=X ∧ (∀ Y:Land, porch S Y F∈ layer (Pairs (Cylinder.Nearest S 6)) s) ∧ ∀ (k m r:ℕ), used_bound S r→ Lease r k m g (fun Y=>porch S Y F)
def Draft (X:Drape)(g s:ℕ):Prop:= ∀ᶠ S:Stenc in atTop, Book S X g s
lemma unit_p (S:Stenc)(V:Land) : porch S V (1:Cylinder.Formula S 6)=1:=by change porch S V (_ ⊗ₜ[ℂ] _) = _; rw [porch_air,map_one,one_smul]
lemma birth0 : Draft 1 0 0:=Eventually.of_forall fun S=>⟨1,by
    funext n o; apply ContinuousMap.ext; intro U; rw [granting,unit_p,map_one]; rfl, fun V=>by rw [unit_p]; simpa only [Finset.card_empty,mono_empty] using Grass.homogeneous (∅:Finset (Pairs (Cylinder.Nearest S 6))), fun k m r hv=>by simp_rw [unit_p]; exact Lease.cup _⟩ -- membership by homogeneous
lemma drought (g s:ℕ):Draft 0 g s:=Eventually.of_forall fun S=>⟨0,funext fun n=>funext fun o=>map_zero _,fun V=>by simp,fun k m r hv=>by simp_rw [map_zero]; exact Lease.nil⟩
lemma Draft.joins {X Y :Drape}{g s:ℕ} (h:Draft X g s)(hx:Draft Y g s):Draft (X+Y) g s:=by
    filter_upwards [h,hx] with S h hh; obtain ⟨F,rfl,hf,hF⟩:=h.funded; obtain ⟨P,rfl,hp,hP⟩:=hh.funded; exact ⟨F+P,funext fun n=>funext fun o=>map_add (Realize.placed S n o) ..,fun i=>by rw [map_add]; exact Submodule.add_mem _ (hf _) (hp _),fun k m r hv=>by simp_rw [map_add]; exact (hF k m r hv).add (hP k m r hv)⟩
lemma Draft.sums {I:Type}(x:Finset I)(f:I→Drape){g s:ℕ}(h:∀ i∈ x,Draft (f i) g s) : Draft (∑ i ∈ x,f i) g s :=by
   induction x using Finset.induction_on with
   | empty=> rw [sum_empty]; exact drought ..
   | insert a x ha ih=> rw [sum_insert ha]; exact Draft.joins (h _ (mem_insert_self ..)) (ih fun i hi=>h _ (mem_insert_of_mem hi))
lemma Draft.scale {X:Drape}{g s:ℕ}(h: Draft X g s)(x:ℂ): Draft (x • X) g s:=by
   filter_upwards [h] with S h; obtain ⟨F,rfl,hf,hF⟩:=h.funded; refine ⟨x • F, funext (fun n=>funext fun o=>map_smul (Realize.placed S n o) ..),fun Y=>by rw [map_smul]; exact Submodule.smul_mem _ _ (hf _),fun k m r hv=>?_⟩; simp_rw [map_smul]; let L:= ((x • LinearMap.id (M:=Dirac (Cylinder.Nearest S 6)) (R:=ℂ)).restrictScalars ℝ).toContinuousLinearMap; exact (hF k m r hv).linear L
lemma Draft.mulX {X Y:Drape}{g s k m:ℕ}(h:Draft X g s)(hx:Draft Y k m): Draft (X*Y) (g+k) (s+m):=by
    filter_upwards [h,hx] with S h hh; obtain ⟨F,rfl,hf,hF⟩:=h.funded; obtain ⟨D,rfl,hp,hD⟩:=hh.funded; refine ⟨F*D, ?_,fun Y=>by rw [porch_house]; exact Grass.layer_mul (hf _) (hp _),fun k m r hv=>by simp_rw [porch_house]; exact (hF k m r hv).product (hD k m r hv)⟩; funext n o; apply ContinuousMap.ext; intro U; change grant _ _ n o U=(grant S F n o U)*(grant S D n o U); rw [granting,granting,granting,porch_house,map_mul]
-- readiness of slot
abbrev ico (i:su.ColorIndex): su.Color:= EuclideanSpace.basisFun su.ColorIndex ℝ i
noncomputable def tendency (s:Slot)(i:su.ColorIndex): Drape:= fun n o=>⟨fun U=> slotted su s i (expandAt (wrap n o) U) • 1, by
    have hf:Continuous (slotted su s i):= Push.Mark.power_cont (solo_chip s i)
    exact Continuous.smul (Push.Mark.onStencil (wrap n o) hf) (continuous_const (y:=(1:Lat.Fields n 6)))⟩
lemma ratedS (s:Slot)(i:su.ColorIndex):Draft (tendency s i) 1 0:=by
   filter_upwards [eventually_ge_atTop s.stencil] with S hS
   obtain ⟨p,hp⟩:= Work.G06.entryPoly_slot s hS i; let F:= p⊗ₜ[ℂ] (1:Dirac (Cylinder.Nearest S 6)); have he(i':Land): porch S i' F=(↑(s.eval i' i):ℂ) • (1:Dirac (Cylinder.Nearest S 6)):= by rw [porch_air,hp]
   refine ⟨F,?_,fun x=> by rw [he]; exact Submodule.smul_mem _ _ (by simpa only [Finset.card_empty,mono_empty] using Grass.homogeneous (∅:Finset (Pairs (Cylinder.Nearest S 6)))),?_⟩
   · funext n o; apply ContinuousMap.ext; intro U; rw [granting,he,map_smul,map_one]; rfl
   intro k m r hx; let L:= (((LinearMap.toSpanSingleton ℂ (Dirac (Cylinder.Nearest S 6)) 1).restrictScalars ℝ).toContinuousLinearMap.comp Complex.ofRealCLM).comp (EuclideanSpace.proj i); simp_rw [he]; refine (?_:Lease r k m 1 (s.eval (G:=su))).linear L
   obtain ⟨C,hC,h⟩:=Work.G07.paid_slot (k:=k) (P:=m) (G:=su) s (show s.stencil⊆S from hS); refine ⟨C,hC,fun p n o hn hp=>?_⟩ ; have hl:=h p hp n o; refine ⟨hl.smooth, mul_nonneg hC (pow_nonneg p.threshold_pos.le _),fun l hl' hD U hv=>?_⟩; simpa only [pow_zero, one_pow, mul_one, Function.comp_def] using hl.bound l hl' hD U (hv.mono_left (Permit.halos S _ (by omega : r≤ r+1) o hx))
-- porch spaces for transported beam.Necessary Lease=0, use path.P
noncomputable def burnish (w:Walk)(q:Bool)(i:Dike): Drape:=fun n o=> cane n q o w i
lemma tones (X:su.El)(g:Cover) (t:Bool)(U:Grid n)(i j:Dike): peggle t (stripe n o w U) i j=Cylinder.ap n (capEdge o w)* peggle t (clutch (haloW n o w U)) i j:=by
   cases t; rfl
   simp only [peggle,if_true,stripe,star_smul,stripe_star,Matrix.transpose_apply,Matrix.smul_apply,smul_eq_mul]
open Paper
lemma kitT (i j:Dike): LP (fun Y:Land=> clutch (Lattice.travel Y 0 w) i j):=by
   unfold clutch blux Lat.copies; simp only [Matrix.blockDiagonal_apply]; split_ifs; next h=> unfold Lat.touch; simp only [Matrix.kroneckerMap_apply]; apply LP.mul (fixLP _); exact traveling ..
   exact fixLP _
lemma brew (q:Bool)(i:Dike): Draft (burnish w q i) 0 1:=by
   let f(j:Dike)(Y:Land):= peggle q (clutch (Lattice.travel Y 0 w)) i j; have hv(j): ∀ᶠ S:Stenc in atTop, Work.G06.EntryPoly S (f j):=by
      unfold f; cases q; exact kitT w _ _; exact (kitT w i j).mono (fun k h=> Work.G06.entryPoly_conj h)
   filter_upwards [eventually_ge_atTop ({stop (0:Cover) w}:Stenc),eventually_all.mpr hv] with S hs hS; let A:↥S:=⟨stop 0 w, Finset.singleton_subset_iff.mp hs⟩; let z(j:Dike):Dirac (Cylinder.Nearest S 6):= lineT q (RP.place A j); let F(Y:Land):=∑ j, f j Y • z j; have ht:= Ford.seriesL Finset.univ (fun j Y=> f j Y • z j) (fun j _=> Ford.plusEP _ (hS j)); obtain ⟨D,hD⟩:=ht; have hQ(Y): porch S Y D=F Y:=congr_fun hD Y
   refine ⟨D,?_,fun V=>by rw [hQ]; exact Submodule.sum_mem _ (fun i _=>Submodule.smul_mem _ _ (by cases q <;> apply Grass.atom_mem)), fun k m r h=>?_⟩
   · funext n o; apply ContinuousMap.ext; intro U; rw [granting,hQ]; unfold F; rw [map_sum]; change _= beams q n o w U i; unfold beams; refine Finset.sum_congr rfl (fun j _=> ?_); rw [map_smul,tones o w 1 0] -- likely sig
     have h : tongue (c:=n) S o (z j)=Cylinder.ap n (capEdge o w) • lineT q (RP.place (landsE n o w) j):=by cases q; exact mouthP ..; exact mouthK ..
     rw [h,smul_smul,mul_comm]; rfl
   simp_rw [hQ]; unfold F; refine Lease.wealth _ _ (fun j _=>?_); let L:= ((LinearMap.toSpanSingleton ℂ (Dirac (Cylinder.Nearest S 6)) (z j)).restrictScalars ℝ).toContinuousLinearMap; exact (Permit.ground S (hS j) r k m).linear L
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.brew
