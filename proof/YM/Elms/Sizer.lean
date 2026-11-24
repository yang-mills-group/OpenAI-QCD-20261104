import YM.Elms.Pulse
/-!
# Span of all equation pivots using large-address linear reads in fixed cutoff symbol algebra.
We ONLY test dimension after invariant projection. (No equivariance assumpts.)
Multipliers test positions also on cover excluding one address: gauge/spin. These proofs don't
need angular data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
-- slopes h=1/(n+1). Off-center.Criterion
noncomputable def tabula (i:ℕ) := (((i+1:ℕ):ℝ))⁻¹
lemma rise0 (i:ℕ) :0 < tabula i:=by unfold tabula; positivity
lemma tab_zero : Tendsto tabula atTop (𝓝 0) :=tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)) -- names
noncomputable def fronts (b:Cover)(i:ℕ):Cover:= ((i+1)^2) • b
lemma pos_front (b:Cover)(i:ℕ): tabula i^2 • vector (fronts b i)=vector b:=by ext1 j; simp only [fronts,tabula,vector, WithLp.ofLp_toLp,PiLp.smul_apply, Pi.smul_apply,nsmul_eq_mul]; push_cast; simp only [smul_eq_mul]; field_simp
abbrev miniR (d:ℕ) : Pol d →ₗ[ℂ] Label d:= brighten d ∘ₗ setas d
variable {d:ℕ}
namespace SparK
-- ranks via moving basis
open LinearMap
variable (R: Submodule ℂ (Label d))
def Scales (i:ℕ):Submodule ℂ (Label d):= R.map (paceL d (tabula i))
def pulls (x:Label d) : Prop:=∃ w:ℕ→Label d,Tendsto w atTop (𝓝 x) ∧ ∀ᶠ j in atTop, w j∈ Scales R j
def crew :Submodule ℂ (Label d) where
   carrier:= {x|pulls R x}
   zero_mem':=⟨0,tendsto_const_nhds,Eventually.of_forall fun i=> Submodule.zero_mem _⟩
   add_mem':=by rintro p q ⟨x,hx,hx'⟩ ⟨y,hy,hy'⟩; exact ⟨x+y,hx.add hy,(hx'.and hy').mono fun j ⟨h₁,h₂⟩=>Submodule.add_mem _ h₁ h₂⟩
   smul_mem':=by rintro c p ⟨x,hx,h'⟩; exact ⟨c • x, tendsto_const_nhds.smul hx,h'.mono fun j h=> Submodule.smul_mem _ _ h⟩
lemma fiscal (U:Submodule ℂ (Label d))(h:U ≤ crew R):Module.finrank ℂ U≤Module.finrank ℂ R:=by
    let m:= Module.finrank ℂ U; let B:=Module.finBasis ℂ U; let X : Fin m→Label d:=fun i=> (B i).val
    have hp(i:Fin m): pulls R (X i):=h (B i).property; choose x hx hX using hp
    have he:LinearIndependent ℂ X:= B.linearIndependent.map' U.subtype U.ker_subtype
    obtain ⟨i,hi,hh⟩:= (((show Tendsto (fun i a=> x a i) atTop (𝓝 X) from tendsto_pi_nhds.mpr hx).eventually he.eventually).and (eventually_all.mpr hX)).exists
    let w: Fin m→ Scales R i:=fun a=>⟨x a i,hh a⟩; have hv: LinearIndependent ℂ w:= by exact LinearIndependent.of_comp (Scales R i).subtype hi
    simpa only [Fintype.card_fin] using le_trans hv.fintype_card_le_finrank (Submodule.finrank_map_le ..)
-- Gauge projection span.Fiscal.L awareness. Choose pre truncated.T separate capacity
open Push.Mark YM.Source YM.Source.Drops
local notation "E"=> d/2
variable (H:Hol su)(hp:∀ k,Peg H k)
noncomputable def glitter (w:Point)(i:su.ColorIndex)(d:ℕ): Pol d:= coarse d (spell (d/2) (positiveLinear H (d/2) w i))
structure Reasons : Prop where
   stamp (w:Point)(i:su.ColorIndex)(p:Pol d) : miniR d (glitter H w i d * p)∈R
   fiber (q:Bool)(i:Pinor)(k:Hue)(u:Flavor 6)(b:Cover)(p:Pol d) : miniR d (flora (Grass.line (Pulses.bent q i k u b))*p)∈R
-- weights exact.Cylinder.Geom
lemma lampT (i:Labels.Key su)(d k:ℕ): drips k (coarse d (MvPolynomial.X i))= if 2 * Labels.generation i ≤ k then coarse d (MvPolynomial.X i) else 0:=by
   let P:PowerPair d:=(Finsupp.single i 1,∅); have he: gen P=coarse d (MvPolynomial.X i):=by simp only [gen,mono_empty,P]; rfl
   have hx:UV.weight P=2*Labels.generation i:=by simp [UV.weight,Labels.height,P,Finsupp.weight_single]
   rw [←he,drips_gen,hx]
lemma capital (j d k:ℕ)(f: AtomAt su j): drips k (coarse d (literal f))= if 2*(j+2) ≤ k then coarse d (literal f) else 0:=by
    unfold literal; obtain ⟨F,hF⟩:=coarseL (d:=d); rw [← hF]; simp_rw [map_sum,map_smul]; rw [hF]; simp only [lampT,Labels.generation]; by_cases h:2*(j+2)≤k<;>simp [h]
lemma lamp2 (i:Labels.Key su)(d k:ℕ): geometry k (coarse d (MvPolynomial.X i))= if 2*Labels.generation i=k then coarse d (MvPolynomial.X i) else 0:=by
   let P:PowerPair d:=(Finsupp.single i 1,∅); have he: gen P=coarse d (MvPolynomial.X i):=by simp only [gen,mono_empty,P]; rfl
   have hx:UV.weight P=2*Labels.generation i:=by simp [UV.weight,Labels.height,P,Finsupp.weight_single];
   rw [←he,geometry_basis,hx]
lemma crownG (j d k:ℕ)(f:AtomAt su j): geometry k (coarse d (literal f))=if 2*(j+2)=k then coarse d (literal f) else 0:=by unfold literal; obtain ⟨F,hF⟩:=coarseL (d:=d); rw [← hF]; simp_rw [map_sum,map_smul]; rw [hF]; simp only [lamp2,Labels.generation]; by_cases h:2*(j+2)=k<;>simp [h]
-- η pre-u.No extension across tests.R
lemma glit_crop {w:Point}{i:su.ColorIndex}{k:ℕ}(h:k ≤ d/2)(h₁:Peg H k)(hP:Peg H (d/2)): drips (2*k) (glitter H w i d)= coarse d (spell k (positiveLinear H k w i)):=by
   rw [← expanded h H w h₁ hP i]
   -- follow Mark.crop
   unfold glitter spell; obtain ⟨F,hF⟩:=coarseL (d:=d); rw [←hF]; simp_rw [map_sum]; rw [hF]; symm
   refine Finset.sum_of_injOn (Fin.castLE (Nat.sub_le_sub_right h 1)) ?_ (fun _ _=>mem_univ _) ?_ ?_
   · rintro ⟨x,hx⟩ _ ⟨y,hy⟩ _ he; simp only [Fin.ext_iff] at *; exact he
   · intro p hi hx
     have H' : k < p.val+2:=by
         rcases p with ⟨p,hp⟩; by_contra! he; change p+2≤k at he; exact hx ⟨⟨p,(by omega)⟩,by simp,rfl⟩
     rw [capital,if_neg (by omega)]
   intro j _; rw [capital,if_pos ?_]; swap
   · change 2*(j.val+2) ≤ 2*k; have ht:=j.isLt; omega
   congr 2; apply LinearMap.ext; intro A; exact congr_arg (positiveLinear H (d/2) w i) (wide_atom h j A)
variable (h:Reasons R H)
-- for any vector in T allowance ideal at top gl total.Stamps
noncomputable def Ore (d:ℕ): Submodule ℂ (Pol d):=Submodule.span ℂ (Set.range (fun x:Point × su.ColorIndex=> glitter H x.1 x.2 d))
include h
lemma OreJobs (f:Pol d) (hp:f∈ Ore H d) (x:Pol d): miniR d (f*x)∈R:=by
   refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
   · rintro _ ⟨⟨j,v⟩,rfl⟩; exact h.stamp _ _ _
   · simp
   · intro a b _ _ ha hb; rw [add_mul,map_add]; exact R.add_mem ha hb
   intro u v _ hV; rw [_root_.smul_mul_assoc,map_smul]; exact R.smul_mem _ hV
omit h
include hp
lemma OreL (w: Ink su) (hw:2*(w.1+2) ≤ d) (hh:Push.Mark.Gap w):∃ g∈ Ore H d, drips (2*(w.1+2)) g=coarse d (literal w.2):=by
   let k:= w.1+2; have ht:=force_span H (hp k) w.2 hh
   let i:Fin (k-1):=⟨w.1,(by unfold k; omega)⟩; let W:=(fun k:Fin (k-1)=>Labels.Taylor su k.val); let L:= w.2 ∘ₗ (LinearMap.proj (φ:=W) i); have he:spell k L=literal w.2 := spell_explicit (d:=k) (j:=i) (G:=su) w.2
   have hm:L∈mounted H k:= ht
   suffices hx: ∀ p: Pulled su k,p ∈ mounted H k→∃ g∈ Ore H d, drips (2*k) g= coarse d (spell k p) by obtain ⟨p,hp,hY⟩:=hx L hm; exact ⟨p,hp,hY.trans (congr_arg _ he)⟩
   intro p hh; obtain ⟨F,hF⟩:=coarseL (d:=d); refine Submodule.span_induction ?_ ?_ ?_ ?_ hh
   · rintro _ ⟨⟨z,m⟩,rfl⟩; exact ⟨_,Submodule.subset_span ⟨(z,m),rfl⟩,glit_crop H (by omega) (hp k) (hp _)⟩ -- h₁ need k tie omega
   · rw [show spell k (0:Pulled su k)=0 from map_zero (spellMap su k),coarse,TensorProduct.zero_tmul]; exact ⟨_,Submodule.zero_mem _,map_zero _⟩
   · rintro a b _ _ ⟨g,hg,hp⟩ ⟨d,h1,h2⟩; exact ⟨g+d,Submodule.add_mem _ hg h1,by rw [map_add,hp,h2,show spell k (a+b)=spell k a+spell k b from map_add (spellMap su _) _ _, ← hF,map_add]⟩
   rintro a b _ ⟨g,hg,hG⟩; refine ⟨(a:ℂ) • g,Submodule.smul_mem _ _ hg,?_⟩; rw [map_smul,hG, show spell k (a • b)=a • spell k b from map_smul (spellMap su _) a b, show a • _=(a:ℂ) • spell k b from (IsScalarTower.algebraMap_smul ℂ a (spell k b)).symm, ← hF,map_smul]
end SparK
end YM.Massive.Elm
