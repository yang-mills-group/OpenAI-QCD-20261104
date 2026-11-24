import YM.VMarker.Eclipse
import YM.MassiveQCD.Lyre.Elevator
/-!
# Handling soft mask terms in marked K transactions
Bank plane implementation. Fixed old unmarked representation. Right Spine.
Soft entries appear precisely when W overlaps flags; we do not substitute an all-flat complement.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Cape
open ConnectedActivityE6 QCD Lattice Finset Wilson RG Pressure Function Filter MeasureTheory NormedSpace
open Sway OrbitG Ruby Kites Grass Lat Cove Push Push.AbsoluteSums Patron
open Cupola Ribbon Loom Loom.Fleet Plate Twist Stitch
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ}{I D Z U:Type}[Fintype I]
-- all marks in relative even Patio.
structure Lure (c:Side)(N:ℕ)(I:Type)[Fintype I](Z:Type) where
    spot:Z→Support c
    wick:Z→Grid c→Tine c N I
    f:Z→Finset I
variable (p:I→Site c)(q:I→Bool) (Y:Lure c N I Z) (F:Film c N I D)(M: Patron.Rail c N U)
structure Lure.On (t:ℝ) : Prop where
    lend j : UsesFinal t (Y.spot j) (Y.wick j)
    meas j: Measurable (Y.wick j)
    expense i V: Y.wick i V ≠0 → ¬ Healthy t (Y.spot i) V
    shades i V: lights (Y.f i) (Y.spot i) p q (Y.wick i V)
    paint i V g: parcelColor N g I (Y.wick i (gauge g V))=Y.wick i V
    stamp i: (Y.f i).image p⊆ Y.spot i
    enough i: (Y.f i).Nonempty
variable {t v:ℝ}
local notation "K"=> Keys c N
local notation "R"=> Ribbon.Spine I
local notation "Φ"=> banknote N p v
local notation "Sh"=> withdraw N p v
local notation "φ"=> rootR R (Keys c N)
noncomputable def torah (v:ℝ) : Rail c (ample N I) (U⊕D) :=⟨Film.addressSets N F M,fun i U=>banknote N p v (Film.spruced N F M i U)⟩
noncomputable def vesta (v:ℝ): Ruby.Hue c (ample N I) Z:=⟨Y.spot,fun i U=> banknote N p v (Y.wick i U)⟩
local notation "X"=> torah p F M v
local notation "Z'"=> vesta p Y v
noncomputable abbrev Stalk (v:ℝ):= Ruby.Plot (vesta p Y v) (torah p F M v)
local notation "P"=> Stalk p Y F M v
noncomputable abbrev tagH (i:U⊕D):=Sum.elim (fun _=>∅) F.z i
noncomputable def corn (i:Z ⊕ D): Finset I:=Sum.elim Y.f F.z i
noncomputable def exitA (i:(U⊕D)⊕Z): Finset I := Sum.elim (tagH F) Y.f i
noncomputable def fog (v:ℝ)(x:Stalk p Y F M v):Finset I:=x.val.biUnion (exitA Y F)
local notation "Γ"=> fog p Y F M v
variable (hY:Y.On p q t) (hF:F.Beat N p q t)(hM:M.Reg t)(hC:∀ i,Cove.shadeG (M.warp i))(hP:0<v)
lemma bankG {V:Tine c N I}{T:Support c}{r: Finset I} (h:lights r T p q V)(hp:r.image p⊆ T): Gated T (banknote N p v V):=by
   change Ribbon.pen N p v V.val ∈ _; rw [← h.1.exact]; apply Ribbon.entitled
   exact h.2 _
   intro j hj; exact hp (mem_image_of_mem _ (Ribbon.located q _ _ hj))
include hF hM
lemma tonic : Rail.Reg X t:=by
   let E:=banknote N p v; refine ⟨?_,?_,?_,?_⟩
   · rintro (u|i) V W he ht; exact congr_arg E (congr_arg (φ) (hM.uses u V W he ht)); exact congr_arg E (hF.reads i V W he ht)
   · rintro (u|i); exact E.toLinearMap.toContinuousLinearMap.measurable.comp ((φ).toLinearMap.toContinuousLinearMap.measurable.comp (hM.reads u)); exact E.toLinearMap.toContinuousLinearMap.measurable.comp (hF.matters i)
   · rintro (u|i) V; apply bankG p q (Twist.crest_l p q _ _ (hM.role u V)); simp; exact bankG p q (hF.budget i V) (hF.spark i)
   · rintro (u|i) V he; exact hM.buys u V (fun hp=>he (by change Φ (φ (M.warp _ _))=0; rw [hp,map_zero,map_zero])); exact hF.mask i V (fun hp=>he ((congr_arg E hp).trans (map_zero _)))
omit hF hM
include hY
lemma vespers : Ruby.Hue.Tall Z' t:=by
   let E:=banknote N p v
   exact ⟨fun i U V hu hv=>congr_arg E (hY.lend i U V hu hv),fun i=> E.toLinearMap.toContinuousLinearMap.measurable.comp (hY.meas i),fun i V he=> hY.expense i V (fun h=>he ((congr_arg E h).trans (map_zero _))),fun i V=> bankG p q (hY.shades i V) (hY.stamp i)⟩
include hF hM hP
local notation "T!"=> Trail Z' X t
noncomputable def tender (V:Grid c)(j:(U⊕D)⊕Z): Tine c N I:= Sum.elim (fun i=>Film.spruced N F M i V) (fun i=>NormedSpace.exp (Y.wick i V)-1) j
lemma tint (j:(U⊕D)⊕ Z)(V:Grid c): Sh (flower Z' X V j)= tender Y F M V j:=by
     rcases j with i|i; exact Cupola.home N _ _ hP _
     change Sh (NormedSpace.exp (banknote N p v (Y.wick _ _))-1)=_
     rw [map_sub,map_one,map_exp (Sh) (Sh).toLinearMap.toContinuousLinearMap.continuous,Cupola.home N _ _ hP]; rfl
lemma innerP (i:P)(V:Grid c): lights ((Γ) i) (scopeK Z' X i.val) p q (Sh ((T!).warp i V)):=by
    change lights _ _ _ _ (Sh (payer ..)); unfold payer; split; swap; · rw [map_zero]; exact ⟨polite_nil ..,clad.nil _⟩
    rw [map_prod]; apply Stitch.Tablet.candlehouse; intro j hj; have hk:=subset_biUnion_of_mem (footD Z' X) hj; rw [tint p q Y F M hY hF hM hP]; rcases j with (i|i)|i
    · have he := Twist.crest_l p q _ _ (hM.role i V); exact ⟨he.1,he.2.raise (limitsMon _ _ hk)⟩
    · obtain ⟨hf,hx⟩:=hF.budget i V; exact ⟨hf,hx.raise (limitsMon _ _ hk)⟩
    have hp:=hY.shades i V; exact ⟨attire hp.1,hp.2.expR.raise (limitsMon _ _ hk)⟩
noncomputable abbrev Cob (v:ℝ):= {i:Stalk p Y F M v// (fog p Y F M v i).Nonempty}
noncomputable def coverP (v t:ℝ): Film c N I (Cob p Y F M v):=⟨fun i=> (Trail (vesta p Y v) (torah p F M v) t).addr i.val,fun i=>fog p Y F M v i.val,fun i V=>withdraw N p v ((Trail (vesta p Y v) (torah p F M v) t).warp i.val V)⟩
local notation "H"=> coverP p Y F M v t
include hC
lemma glowP : Film.Beat N p q H t:=by
    let D:=withdraw N p v
    have ht := tonic p q F M (v:=v) hF hM; have hM':=(plant _ _ (vespers p q Y (v:=v) hY) ht)
    refine ⟨fun i=>i.2,?_,fun i=> D.toLinearMap.toContinuousLinearMap.measurable.comp (hM'.reads i.val),fun i U V he hv=>congr_arg D (hM'.uses _ U V he hv), ?_,fun i V hv=> hM'.buys _ _ (fun hh=> hv ((congr_arg D hh).trans (map_zero _))), fun j V=>innerP p q Y F M hY hF hM hP j.val V⟩
    · intro i j hj; obtain ⟨v,hv,rfl⟩:=mem_image.mp hj; obtain ⟨k,hk,hv⟩:=mem_biUnion.mp hv
      suffices h:p v∈footD Z' X k from mem_biUnion.mpr ⟨k,hk,h⟩
      rcases k with (k|k)|k; exact (notMem_empty v hv).elim; exact hF.spark k (mem_image_of_mem _ hv); exact hY.stamp k (mem_image_of_mem _ hv)
    intro i V g; let C:=parcelColor N g I; let x:=scopeK Z' X i.val.val
    change C (D (payer Z' X t _ _))= D (payer Z' X t _ _); unfold payer; rw [gauge_flags]; split; swap; · rw [map_zero,map_zero]
    rw [map_prod,map_prod,map_prod]; apply Finset.prod_congr rfl; intro j _; simp_rw [show ∀ (W:Grid c), D (flower Z' X W j)=tender Y F M W j from fun W=> tint p q Y F M hY hF hM hP j W]; rcases j with (k|k)|k
    · exact Subtype.ext (Twist.root_turn (I:=I) g _ _ (hC k V g))
    · exact hF.color k V g
    change C (NormedSpace.exp (_)-1)=_; rw [map_sub, map_exp C C.toLinearMap.toContinuousLinearMap.continuous,map_one,show C _ =_ from hY.paint k V g]; rfl
end YM.MassiveQCD.Cape
#print axioms YM.MassiveQCD.Cape.glowP
