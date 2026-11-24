import YM.QCD.Pant.Court
import YM.QCD.Land.Council
/-! # Compact symmetrizations for external frames. Gated. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Patron
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{N:ℕ}
local notation "V"=>EvenA c N
lemma gateC (s:Equiv.Perm (Site c))(p: Site c→Lat.Bundle)(v:V)(S:Support c)(h:Gated S v): Gated (S.image s) (sways (copies N (rides s p)) v):=by
   let T:= rides s p; let Z:= S.image s
   have he (i j:Modes c N)(hf:copies N T i j≠0) : s i.1.1 = j.1.1:=by
     rcases i with ⟨⟨a,b⟩,u⟩; rcases j with ⟨⟨d,g⟩,w⟩; unfold T copies at hf; rw [Matrix.blockDiagonal_apply] at hf; split at hf
     next h=> by_contra hz; rw [rr,if_neg hz] at hf; exact hf rfl
     next h=> exact hf rfl |>.elim
   have hh (i: Modes c N)(v:i.1.1∈S): disguise (copies N T) (psi i)∈ region (limits Z)∧ disguise (copies N T) (bar i) ∈region (limits Z):=by
     unfold disguise; rw [adapt_psi,adapt_bar]; apply And.intro
     · apply Subalgebra.sum_mem; intro j _; by_cases ht: copies N T i j=0; · rw [ht, zero_smul]; exact Subalgebra.zero_mem _
       apply Subalgebra.smul_mem; apply marked; refine mem_filter.mpr ⟨mem_univ _,show j.1.1∈ Z from Finset.mem_image.mpr ⟨_,v,he i j ht⟩⟩
     apply Subalgebra.sum_mem; intro j _; by_cases ht: copies N T i j=0; · change star (copies N T i j) • _ ∈ _; rw [ht, star_zero,zero_smul]; exact Subalgebra.zero_mem _
     apply Subalgebra.smul_mem; apply marked; refine mem_filter.mpr ⟨mem_univ _,show j.1.1∈ Z from Finset.mem_image.mpr ⟨_,v,he i j ht⟩⟩
   exact effects (disguise _) (fun i hi=> by cases i with | inl i=> exact (hh i (mem_filter.mp hi).2).1 | inr i => exact (hh i (mem_filter.mp hi).2).2) v.val h
lemma gateS (p:Strut c)(z:Lat.Spike)(d:Site c→ℂ)(v:V)(S:Support c)(h:Gated S v): Gated (S.image (act p)) (Diode N p z d v):=gateC _ (lightP p z d) v S h -- h?
lemma gateL (p:Frame c)(v:V)(S:Support c)(h:Gated S v): Gated S (sways (Lat.rotates N p) v):=by
   let W:= fun i=> touch (colour (p i)); have he:=gateC (Equiv.refl _) W v S h; rw [show S.image (Equiv.refl _)=S from Finset.image_id] at he; exact he
lemma eVoc (M: V →+*V)(hp:Continuous M)(he:Bijective M){ι: Type*}[MeasurableSpace ι](v:ι→V)(μ: Measure ι): M (∫ i,v i ∂μ)=∫ i,M (v i) ∂μ:=by
    let X:= M.toAddMonoidHom.toRealLinearMap hp
    let Y:EvenA c N ≃L[ℝ] EvenA c N:= (LinearEquiv.ofBijective X.toLinearMap he).toContinuousLinearEquiv
    exact (Y.integral_comp_comm v).symm

def brine (c:Side): Measure (Frame c):=Measure.pi fun _:Site c=>su.probHaar
instance brine_one : IsProbabilityMeasure (brine c):=by unfold brine; infer_instance
def pepper (f:Grid c→EvenA c N)(U:Grid c):EvenA c N:=∫ z:Frame c,sways (Lat.rotates N z) (f (Lattice.gauge z U)) ∂ brine c
lemma wharf (f:Grid c→V)(h:Measurable f): Measurable (pepper f):=by
   have hp:Measurable fun i:Grid c×Frame c=> gauge i.2 i.1:=by refine measurable_pi_lambda _ fun i=> ?_; unfold Lattice.gauge; fun_prop
   have ht:= (Land.turn_c (X:=Site c) (F:=N)).measurable
   let p (x : Grid c × Frame c):= sways (Lat.rotates N x.2) (f (Lattice.gauge x.2 x.1))
   let q (x:Grid c × Frame c):= (x.2, light (Keys c N) (f (gauge x.2 x.1)))
   have hf:Measurable q:=measurable_snd.prodMk ((lightC (Keys c N)).measurable.comp (h.comp hp))
   have hc: Cove.light (Keys c N) ∘ p= (fun a=> Land.turnin a.1 N a.2) ∘ q:=rfl
   have hh: Measurable (fun x=> (p x).val):=by change Measurable (Cove.light (Keys c N) ∘ p); rw [hc]; exact ht.comp hf
   have hv : Measurable p:= Measurable.subtype_mk hh
   exact (hv.stronglyMeasurable.integral_prod_right' (ν:=brine c)).measurable
lemma siteZ (f:Grid c→V)(A:Support c)(ht:LocalOn A f): LocalOn A (pepper f):=by
    intro U W he; unfold pepper; apply integral_congr_ae; filter_upwards with z; apply congr_arg; refine ht _ _ ?_; intro i hv ht'; unfold Lattice.gauge; rw [he i hv ht']
lemma shaded (f:Grid c→V):shadeG (pepper f):=by
    intro U z; suffices H:sways (Lat.rotates N z) (pepper f (gauge z U))=pepper f U by exact congr_arg Subtype.val H
    let Q:=MeasurableEquiv.piCongrRight (fun i=> MeasurableEquiv.mulRight (z i)); have hp : MeasurePreserving Q (brine c) (brine c):= measurePreserving_pi _ _ (fun i : Site c=> measurePreserving_mul_right su.probHaar (z i))
    unfold pepper; rw [eVoc _ (phare _) (surfeit (rotates_law ..)),← hp.integral_comp' (fun k=> sways (Lat.rotates N k) (f (gauge k U)))]; apply integral_congr_ae; filter_upwards with u
    have he:gauge u (gauge z U)=gauge (u*z) U:=by funext i; unfold Lattice.gauge; rw [Pi.mul_apply, Pi.mul_apply]; group
    rw [leaps, he]; change _=sways (Lat.rotates N (u*z)) (f (gauge (u*z) U)); rw [show Lat.rotates N (u*z)=_ from (Land.circuits ..)]; rfl
lemma peppy (f:Grid c→V)(t:ℝ)(S:Support c)(h:shadeG (masked t S f)): masked t S (pepper f)=masked t S f:=by
    funext i; by_cases he:Healthy t S i
    · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he]; unfold pepper; have hx k:sways (Lat.rotates N k) (f (Lattice.gauge k i))= f i:=by
          have hh : Healthy t S (Lattice.gauge k i):=by unfold Healthy; rw [gauge_flags]; exact he
          have hk:=h i k; rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ hh] at hk; exact Subtype.ext hk
      simp_rw [hx]; simp
    rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he]
lemma nursery (f: Grid c→V)(h:∀ i,Fit (f i)):∀ i, Fit (pepper f i):=by
   intro i W hW; unfold pepper; rw [eVoc _ (phare _) (surfeit (unit_f hW))]; apply integral_congr_ae; filter_upwards with z; exact polarizei _ (h _) _ W hW
lemma estate (f:Grid c→V)(h:∀ i,Regal c N (f i)=f i) (U:Grid c): Regal c N (pepper f U)=pepper f U:=by
   unfold pepper; rw [eVoc _ (phare _) (imp _ (gammaL ..))]; apply integral_congr_ae; filter_upwards with z; rw [gaugeS,h]
lemma plotP (f:Grid c→V)(A: Support c)(h:∀ U,Gated A (f U))(U:Grid c): Gated A (pepper f U):=Territory.froth A _ (fun z=> gateL z _ A (h _)) _
end YM.QCD.Patron
