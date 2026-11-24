import YM.Sprig.IceW
/-! Composable stencil measurements. Include replicated-price vocabulary for later phase usage, but no assertion of their limits. -/
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
-- Glyph orientations source costs.Inj.Actual norm.
structure Compass (C:Sequence)(D:ℕ) where
   (L:Side) (Hp:Dial D)(z:ℝ)(pA pB i ℓ m Uq w K q:ℕ)(e v H:ℝ)(Ω:Finset (Glyph D))
namespace Compass
variable (A:Compass C D) (k:ℕ)
noncomputable abbrev r:ℝ:= sharpM C.S A.L A.Hp A.z A.i
noncomputable abbrev dB:ℝ:= reserved A.L A.Hp A.w A.z
noncomputable abbrev bid:ℝ:= minorV A.L A.q A.z
noncomputable abbrev qR (j:ℕ):Cover→ E4:=screen C.S j A.r
-- notation Δ steps
structure Known (A:Compass C D):Prop where
   Γ : Tier C.S A.L A.Hp A.z A.i A.ℓ A.pA A.pB A.w
   width : Promises A.L A.Hp A.w A.Uq A.m A.K A.q A.e A.v A.H A.z
   live : 0<A.e
   space : 0<A.v
   paid : 1 ≤ A.H
   hefty : 2≤ A.K
   plugs (n:ℕ)(x:Fin n→Glyph D)(hx:n≤A.K)(hX:∀ i,x i∈A.Ω): Faucet A.e A.v x A.H
lemma realH : 0 < r A:= Tier.realH ..
-- handle side valuations and finite regulators
variable (Z: ∀ d:ℕ,Label d→ₗ[ℂ] Label d)
local notation "Sn"=> C.S.side (C.R k) (C.N k)
noncomputable abbrev treeX (X:Fin n→ Glyph D)(y:Fin n→ Cover)(j:Fin n):Insertion (C.S.side (C.R k) (C.N k)) 6:= P.physical none k (Z (X j).width (X j).material) (y j) -- A absent
noncomputable abbrev hike (b:Cover):Cover:= ratioTo C.S (C.N k) A.ℓ • b
noncomputable abbrev checkW(X:Fin n→ Glyph D)(y:Fin n→ Cover)(j:Fin n):Stud (C.S.side (C.R k) (C.N k)) 6:= treeX P k Z X (A.hike k ∘ y) j
structure Plot (A:Compass C D)(k:ℕ)(Z:∀ d:ℕ,Label d→ₗ[ℂ] Label d):Prop where
   stage : A.i ≤ C.N k
   rich: ∀ d,d≤ D→Skin P.sym d (Z d)
   here (n:ℕ) (X:Fin n→ Glyph D)(hz:∀ i,X i∈A.Ω)(hx:∀ i,(X i).material≠0)(hw:n≤ A.K)(y:Fin n→ Cover)(hy:A.qR A.ℓ ∘ y ∈ Ibis.flats (Fin n) (2*A.e) (A.v/2)): ‖(C.A k).regulator.average (List.ofFn (treeX P k Z X (A.hike k ∘ y))).prod - Ibis.candle X (A.qR A.ℓ ∘ y)‖≤ A.bid
   feast (X:Fin 2→ Glyph D)(hz:∀ i,X i∈A.Ω)(hx:∀ i,(X i).material≠0)(y:Cover)(hy:![0,A.qR (C.N k) y]∈ Ibis.flats (Fin 2) (3*A.e) (A.v/4))(hv:∀ a:Axis,2*A.e≤ A.qR (C.N k) y a): ‖(C.A k).regulator.average (List.ofFn (treeX P k Z X (![0,y]))).prod- Ibis.candle X (![0,A.qR (C.N k) y])‖ ≤ A.bid
   segment (n:ℕ) (X:Fin n→ Glyph D)(hz:∀ i,X i∈A.Ω)(hx:∀ i,(X i).material≠0)(hw:n≤ A.K)(y:Fin n→ Cover)(hy:A.qR (C.N k) ∘ y ∈ Ibis.flats (Fin n) (2*A.e) (A.v/2)): ∃ (u:Site (C.S.side (C.R k) A.ℓ))(x:Fin n→ Site (C.S.side (C.R k) A.pB))(hV:A.pB ≤ C.N k)(hp: Even (C.R k).val), let T:= Column.sky C.S (C.R k) A.pB (C.N k) hV (evenW _ _ hp _) u; Injective x ∧ (∀ i, wrap _ (y i)∈ T.margin (x i) (Vista.softerT C.S A.ℓ A.pB (C.N k) A.Uq A.m)) ∧ ∀ j, let V:= treeX P k Z X y j; Fence (T.chamber (x j)) (⇑V) ∧ (∀ W, Hom (polarity (X j).spin) (V W)) ∧ topH T (C.A k).regulator (⇑V) (x j) ≤ A.dB
   proofH (n:ℕ) (X:Fin n→Glyph D)(hz:∀ i,X i∈A.Ω)(hx:∀ i,(X i).material≠0)(hw:n≤ A.K)(ht:0<n)(y:Fin n→ Cover)(hy:A.qR A.ℓ ∘ y ∈ Ibis.flats (Fin n) (2*A.e) (A.v/2)): ∃ (u:Site (C.S.side (C.R k) A.ℓ))(h:A.pA ≤ C.N k)(hp:Even (C.R k).val)(hX:∀ i' W, Hom (weightsT X i') (checkW P A k Z X y i' W)), let T:= Column.sky C.S (C.R k) A.pA (C.N k) h (evenW _ _ hp _) u; let V:= ProbeWords X (List.finRange n) (A.qR A.ℓ ∘ y) (checkW P A k Z X y) hX; Fence (T.chamber (0:Site (C.S.side (C.R k) A.pA))) V ∧ Potion V ∧ topH T (C.A k).regulator V (0:Site (C.S.side (C.R k) A.pA)) ≤ A.bid
#check Plot
variable {Vb:YM.Source.Hol su}(Uv: Lining.Temper.Collage.Exhibit Vb)(Θ:SourceRead.TaperHol)(ζ:RawSym)(G:Lining.Temper.Collage.Exhibit.CoreMix)(base:ℕ→ℕ)(Xv εr:ℝ)(pv:ℕ→ℝ)(Zq:ℕ→BudgetPoint)(Dk:ℕ)
variable {β e:ℝ}(ht:C.Path β e)(R0:Vista (C.S.side (C.R k) A.i) D)(hs:A.i≤ C.N k)
set_option quotPrecheck false
local notation "Qv"=> (fun d a=> G d a k)
variable (hk:Known A)(hc : Vista.RoofV (C.A k) R0 hs (ht.even k) ζ A.Ω A.Uq A.K A.e A.v Xv A.Hp A.L A.z A.pA A.ℓ Θ Uv εr Dk Zq pv base (fun d a=>G d a k))
include ht hc hk
lemma comes (hZ:∀ d,d≤ D→Skin ζ d (Z d)∧∀ p:Label d,Attest (C.A k) R0 Θ (base d) p (Z d p))(hKing:∀ X∈ A.Ω, kingT ((Uv.display C Θ ζ G base).stencil X.width)≤ratioTo C.S (C.N k) A.ℓ*A.m)(hN:2*(A.v*measureV A.L A.Hp.e A.z)<((C.S.side (C.R k) A.ℓ).val:ℝ)): Plot (Uv.display C Θ ζ G base) A k Z:=by
    have hh:(C.A k).regulator.Z=Massive.joint ((C.A k).density (C.N k)):=by rw[(ht.normalized k).start]; change Massive.joint (⇑(((C.A k).regulator.density)*1))= _; rw [mul_one]
    have hzP:0 < (C.A k).regulator.Z:=hh.symm ▸ (ht.normalized k).normal (Nat.le_refl (C.N k)); have hf:= (sideW ht k (C.N k)); have h1 := ((ht.normalized k).beta_pos (Nat.le_refl _)).le
    refine ⟨hs,fun _ h=>(hZ _ h).1,fun n X hz hx hw y hy=>?_,fun X hz hx y hy hv=>?_,fun n X hz hx hw y hy=>?_,fun n X hz hx hw ht₁ y hy=>?_⟩
    · exact Vista.cheersG (C.A k) Uv Θ ζ C G R0 A.L A.Ω A.Hp A.z Dk A.Uq A.pA A.ℓ A.K A.e A.v εr Xv Zq pv base (Qv) _ hs hc A.w A.m n A.q Z X hz hx hKing A.H hk.paid (hk.plugs n X hw hz) (fun d h=>(hZ d h).2) hk.Γ hk.width hk.live hk.space hN hw y hzP h1 hf hy
    · have h:= Vista.testR (C.A k) Uv Θ ζ C G R0 A.L A.Ω A.Hp A.z Dk A.Uq A.pA A.ℓ A.K A.e A.v εr Xv Zq pv base (Qv) _ hs hc A.w A.m A.q Z hKing A.H hk.paid (fun d h=>(hZ d h).2) hk.Γ hk.width hk.live hk.space hN hzP h1 hf X hk.hefty hz hx (hk.plugs 2 X hk.hefty hz) y hy hv; simp only [List.ofFn_zero,List.ofFn_succ,List.prod_nil,List.prod_cons,mul_one]; exact h
    · obtain ⟨a,W,h⟩:= Vista.roomP (C.A k) Uv Θ ζ C G R0 A.L A.Ω A.Hp A.z Dk A.Uq A.pA A.ℓ A.K A.e A.v εr Xv Zq pv base (Qv) _ hs hc A.w A.m n A.q Z X hz hx hKing A.H hk.paid (hk.plugs n X hw hz) (fun d h=>(hZ d h).2) hk.Γ hk.width hk.live hk.space hN hw y hzP h1 hf hy; exact ⟨a,W,hk.Γ.ascend.le.trans (hk.Γ.above.le.trans hs),ht.even k,h⟩
    obtain ⟨a,hw,hp',hf',h⟩:= Vista.clubs_glide (C.A k) Uv Θ ζ C G R0 A.L A.Ω A.Hp A.z Dk A.Uq A.pA A.ℓ A.K A.e A.v εr Xv Zq pv base (Qv) _ hs hc A.w A.m n A.q Z X hz hx hKing A.H hk.paid (hk.plugs n X hw hz) (fun d h=>(hZ d h).2) hk.Γ hk.width hk.live hk.space hN hw y hzP h1 hf hy ht₁; exact ⟨a,hw.trans (hp'.trans hs),ht.even k,hf',h⟩
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.comes
