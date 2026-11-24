import YM.Sprig.SkyP
import YM.Rill.Comes
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
variable {C:Sequence} {D d n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV
open Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
open Massive.Elm.SparK.Arbor.PlaneG
namespace Compass
variable (A:Compass C D)
-- per-Compass point alignment earned on P
noncomputable def grace (Z:ℕ→ ∀ d,Label d→ₗ[ℂ]Label d)(φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ]Label d) : Prop:= ∀ d,d ≤ D→∀ v:Label d,Tendsto (fun i=> Z (φ i) d v) atTop (𝓝 (V d v)) -- must include Compass ? uses only D
#check grace
variable (Z:ℕ→ ∀ d,Label d→ₗ[ℂ]Label d)(φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d)(HK:∀ d,Pins d) {β e:ℝ}(ht:C.Path β e)
set_option quotPrecheck false
variable (h:Tendsto φ atTop atTop)(hg: grace (D:=D) Z φ V)(hp:∀ᶠ i in atTop,Plot P A i (Z i))
include A h
-- choose cofinal. Launch skeleton/norm using prior Instance.Rem
lemma picking (G:ℝ) (he: 0 ≤ G)(hV:∀ᶠ i in atTop,∀ d,d ≤ D→ ∀ j:Raw d, ‖Z i d ((HK d).basic j)‖ ≤ G):∃ f:ℕ→ℕ,StrictMono f∧∃ V:∀ d,Label d→ₗ[ℂ] Label d,grace (D:=D) Z (φ ∘f) V:=by
     let F:= Σ d:Fin (D+1), Raw d.val; let L (x:F)(i:ℕ):= Z (φ i) x.1.val ((HK x.1.val).basic x.2)
     obtain ⟨g,hg,v,hV⟩:= YM.Fir.Lantern.armor L (fun x:F=>⟨G,he,h.eventually (hV.mono (fun i hi=>hi _ (Nat.le_of_lt_succ x.1.isLt) _))⟩)
     let W(d:ℕ)(h:d≤ D)(i:Raw d):Label d:= v ⟨⟨d,Nat.lt_succ_of_le h⟩,i⟩; let T (d:ℕ)(h:d ≤ D):= (HK d).basic.constr ℂ (W d h)
     refine ⟨g,hg,(fun d=>if h:d ≤ D then T d h else 0),fun d hd p=>?_⟩; simp only [dif_pos hd]; let X:Fin (D+1):=⟨d,Nat.lt_succ_of_le hd⟩; let f:=(HK d).basic
     let k(j:Raw d):= f.coord j p
     have h'(r:Label d→ₗ[ℂ]Label d): r p=∑ j:Raw d,k j • r (f j):=by simp_rw [← map_smul,← map_sum]; rw[show ∑ j:Raw d,k j • f j=p from f.sum_repr p]
     -- limit commute terms
     rw [show (fun i=>Z ((φ ∘g) i) d p)=(fun i=>∑ j:Raw d,k j • Z (φ (g i)) d (f j)) from funext fun i=>h' (Z _ d)]
     have ht':T d hd p=∑ j:Raw d,k j • W d hd j:=by rw[h' (T d hd)]; simp only [T,f, Module.Basis.constr_basis]
     rw[ht']; exact tendsto_finset_sum _ fun j _=> (hV ⟨X,j⟩).const_smul (k j)
include hp hg
lemma outfits {d:ℕ}(he:d ≤ D): Skin P.sym d (V d):=by
    let x' := P.sym; let vp(p:Label d)(i:ℕ):=Z (φ i) d p; let Zt(p:Label d):= V d p; have hm(p:Label d): Tendsto (vp p) atTop (𝓝 (Zt p)):=hg d he p
    have hp':∀ᶠ i:ℕ in atTop, Skin P.sym d (Z (φ i) d):= h.eventually (hp.mono fun i hi=> hi.rich d he)
    refine ⟨fun x p s ht=> tendsto_nhds_unique (hm _) ?_, fun x a=> tendsto_nhds_unique (hm _) ?_, fun x=> tendsto_nhds_unique (hm _) ?_,fun x u=> tendsto_nhds_unique (hm _) ?_,fun x=> tendsto_nhds_unique (hm _) ?_, tendsto_nhds_unique (hm _) ?_⟩
    · have ht' : Continuous ⇑(x'.pin d p):=by
            exact (x'.pin d p).toLinearMap.continuous_of_finiteDimensional
      exact ((ht'.tendsto _).comp (hm x)).congr' (hp'.mono (fun i hi=>(hi.pin x p s ht).symm))
    · have ht' : Continuous ⇑(x'.adj d a):=by
            let F:=x'.adj d a; let B:=Module.finBasis ℂ (Label d)
            have he(p:Label d): F p= ∑ j, star (B.coord j p) • F (B j):=by nth_rw 1 [← B.sum_repr p]; simp only [map_sum,map_smulₛₗ]; rfl
            rw [show ⇑(x'.adj d a) = _ from funext he]; exact continuous_finset_sum _ fun i _=> (continuous_star.comp ((B.coord i).continuous_of_finiteDimensional)).smul continuous_const
      exact ((ht'.tendsto _).comp (hm x)).congr' (hp'.mono (fun i hi=>(hi.adj x a).symm))
    · have ht' : Continuous ⇑(x'.charge d):=by
            exact (x'.charge d).toLinearMap.continuous_of_finiteDimensional
      exact ((ht'.tendsto _).comp (hm x)).congr' (hp'.mono (fun i hi=>(hi.charge x).symm))
    · have ht' : Continuous ⇑(x'.flavor d u):=by
            exact (x'.flavor d u).toLinearMap.continuous_of_finiteDimensional
      exact ((ht'.tendsto _).comp (hm x)).congr' (hp'.mono (fun i hi=>(hi.flavor x u).symm))
    · have ht' : Continuous ⇑(x'.parity d):=by
            exact (x'.parity d).toLinearMap.continuous_of_finiteDimensional
      exact ((ht'.tendsto _).comp (hm x)).congr' (hp'.mono (fun i hi=>(hi.parity x).symm))
    exact tendsto_const_nhds.congr' (hp'.mono (fun i hi=>hi.unit.symm))
structure Pod (P:Calibration C)(A:Compass C D)(φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d):Prop where
    proc : ∃ (g:ℕ→ℕ)(Z:ℕ→∀ d,Label d→ₗ[ℂ] Label d), StrictMono g∧ grace (D:=D) Z (φ ∘g) V∧∀ᶠ i in atTop,Plot P A i (Z i)
include h
omit hp hg
lemma Facing (hc:∃ F:ℝ,0 ≤ F ∧∀ᶠ i in atTop,∃ Z:∀ d:ℕ,Label d→ₗ[ℂ] Label d, Plot P A i Z ∧ ∀ d:ℕ,d≤ D→ ∀ p:Raw d, ‖Z d ((HK d).basic p)‖ ≤ F):∃ V:∀ d,Label d→ₗ[ℂ] Label d, Pod P A φ V:=by
     obtain ⟨F,hF,hc⟩:=hc; obtain ⟨N,hN⟩:= eventually_atTop.mp hc; choose! Z hZ hX using hN
     obtain ⟨g,hg,V,hV⟩:= picking A Z φ HK h F hF (eventually_atTop.mpr ⟨N,hX⟩); exact ⟨V,⟨g,Z,hg,hV,eventually_atTop.mpr ⟨N,hZ⟩⟩⟩
end Compass
end YM.Intag.Sprig
#check YM.Intag.Sprig.Compass.picking
#print axioms YM.Intag.Sprig.Compass.outfits
#print axioms YM.Intag.Sprig.Compass.Facing
