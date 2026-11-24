import YM.Sprig.Moats
import YM.Lust.Treasure
/-! Additional after-L requests for free tracking.
These are a polynomial number of transfer orders per finite family, just the costs supported by the actual clocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF Massive.Elm.SparK.Arbor.PlaneG
variable (φ:ℕ→ℕ)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
open Function Set Finset Metric Compass
variable (sy:RawSym)(t:ℕ)(L:Side)(Hp:Dial D)(Ω:Finset (Glyph D))(La:∀ d,Laurel d)(J:∀ d,Landing sy (La d))(m K U q:ℕ)(e v:ℝ)
noncomputable def weightV (z:ℝ):=t+reserved L Hp 2 z
noncomputable def numberQ (n:ℕ):ℝ:= ((n:ℝ)+1)⁻¹
lemma decay: Tendsto numberQ atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop _ tendsto_natCast_atTop_atTop) -- arity order
lemma vv(j:ℕ):0 < numberQ j:=by unfold numberQ; positivity
structure Seek (z:ℝ) :Prop where
     canopy : ∃ G:ℝ, 1 ≤ G∧(∀ n≤K,∀ x:Fin n→ Glyph D,(∀ i,x i∈ Ω)→Faucet e v x G)∧ Promises L Hp 2 U m K q e v G z
     choice (j:ℕ)(h:j≤ D): minorV L q z ≤ (J j).ε/4
     small : (weightV t L Hp z)^t * minorV L q z ≤ numberQ t
     near : (weightV t L Hp z)^t * (measureV L Hp.e z)⁻¹ ≤ numberQ t
     roof : (measureV L 4 z)⁻¹≤ numberQ t
#check Seek
include J
lemma scout (hb:100*(K+1) ≤ U)(he:0<e)(hv:0 < v)(hL:1<L.val)(hq: 11< q)(hR:q< Hp.R)(hE:Hp.R<Hp.e):∀ᶠ z in atTop,Seek sy t L Hp Ω La J m K U q e v z:=by
    have hv' :∀ᶠ G:ℝ in atTop,∀ n≤K, ∀ x: Fin n→ Glyph D, (∀ i,x i∈ Ω)→ Faucet e v x G:=by
              have hh(n:Fin (K+1))(x: Fin n.val→↥Ω) :∀ᶠ G in atTop,Faucet e v (fun i=>(x i).val) G:= dawn e v _ he -- binder atlas. subtype.Finite!
              refine (eventually_all.mpr (fun i=> eventually_all.mpr (hh i))).mono ?_
              intro G HG n h x hp
              exact HG (⟨n,Nat.lt_succ_of_le h⟩) (fun i=> ⟨x i,hp i⟩)
    obtain ⟨G,hG,H⟩:= ((eventually_ge_atTop (1:ℝ)).and hv').exists
    have ht:PageP L (fun z=> (weightV t L Hp z)^t) 11:= ((PageP.just L t 11).harm L (riseT L Hp 2)).liftNat L t
    have hz:Tendsto (minorV L q) atTop (𝓝 0):=tendsto_inv_atTop_zero.comp (tonicV L hL (by omega))
    have hx:Tendsto (minorV L 4) atTop (𝓝 0):= tendsto_inv_atTop_zero.comp (tonicV L hL (by omega))
    filter_upwards [eventually_all.mpr (fun i:Fin (D+1)=> hz.eventually_le_const (div_pos ((J i).light) (by norm_num:(0:ℝ)<4))), ht.absorb L hL hq _ (vv t),ht.absorb L hL (show 11<Hp.e from by omega) _ (vv t),hx.eventually_le_const (vv t), Ibis.fig L Hp 2 U m K q e v G hL hb hE (by omega) hR (by norm_num) he hv hG] with z hz h h' hv hS
    exact ⟨⟨G,hG,H,hS⟩,fun i hi=> hz ⟨_,Nat.lt_succ_of_le hi⟩, (div_eq_mul_inv ..).symm.trans_le h,(div_eq_mul_inv ..).symm.trans_le h', hv⟩
omit J
lemma atlas_cost (A:Compass C D)(h:Known A) : A.r ≤ (measureV A.L 4 A.z)⁻¹:=by
    let t:= measureV A.L A.Hp.e A.z; let p:=measureV A.L 4 A.z; let q:= measureV A.L (Dial.βA A.Hp) A.z; have hp:0<p:=χone ..; have ht:0 < t:=χone ..; have hq:1≤q:=uniformV ..
    have h1:= h.Γ.rise_step (h.Γ.lower.trans h.Γ.ascend.le); rw [h.Γ.shadows,h.Γ.rep] at h1
    let r:= r A; have he:0< r:= A.realH; have hv:C.S.spacing A.pA≤1:=inv_le_one_of_one_le₀ (show 1 ≤ ((C.S.ratio _).val:ℝ) from (by exact_mod_cast (C.S.ratio A.pA).pos))
    have h2:C.S.spacing A.pA/r=t⁻¹*(p*(q*t)):= h1.symm
    field_simp at h2; change r≤ p⁻¹; field_simp; nlinarith only [hq, hv,h2,he,hp,mul_pos hp he,mul_le_mul_of_nonneg_left hq (mul_pos hp he).le]
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Seek
#print axioms YM.Intag.Sprig.scout
#print axioms YM.Intag.Sprig.atlas_cost
