import YM.Alum.Pulps
import YM.Patria.Orchid
import YM.Eden.Bonus
import YM.Arise.Pair
/-! From a single posture obtain all of the linear matches. True unit Tally and sym orientation. Normalization in the actual candidate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth QCD QCD.Tide Tarot QCD.Lat QCD.Grass
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator
variable {S:Scheme}{R:Side}{i ℓ k p N j:ℕ}{c:Side}{D d:ℕ}(A:Massive.Run S N R 6)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar
open Poised Sieve Plans Plans.Stamp SourceRead
open UV
noncomputable abbrev ncl(d:ℕ)(V:Vista (S.side R i) D): Matrix.IsSymm (milky 0 V.H (S.side R i) (G:=su) (d':=d)):= milky_symm _ V.ht V.ha -- Prop vs term!
variable (V:Vista (S.side R i) D)
noncomputable def lantern (d:ℕ) (u:Label d): Cover → Insertion (S.side R i) 6:= (lotus d V.H _ V.Q (ncl (R:=R) (i:=i) _ V) V.w V.η u.val) _
-- view literal pair.
noncomputable def lung(d:ℕ):Label d →ₗ[ℂ]Cover → Insertion (S.side R i) 6 where
    toFun:= lantern V d
    map_add' x y:=by unfold lantern; rw [Submodule.coe_add,map_add]; rfl
    map_smul' t x:=by unfold lantern; rw [SetLike.val_smul,map_smul]; rfl
local notation "Φ"=> (lung V)
local notation "Sn"=>S.side R
variable (sym:RawSym)
open Massive.Cylinder
lemma aperture(X:Glyph D) : (tokenP X V:ℂ) • Vista.spire X V = lantern V X.width X.material:=by -- ar check
    let t:= tokenP X V; have hp:0<t:= Massive.Evo.dollar0 X.eng X.gauge X.spin V.hw V.he V.R.threshold_pos V.hb
    funext b; exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr hp.ne') _
include sym
lemma lute(d:ℕ)(b:Cover): (lung V d) (sym.unit d) b = 1:=by
     ext1 U; change lotus d V.H _ V.Q (ncl (i:=i) _ V) V.w V.η (sym.unit d).val _ b U=1; rw [sym.unitActs]; unfold UV.unit; rw [leafs_t]; simp only [map_one,YM.Next.Rank.Normal.pure, one_smul]; rw[show QCD.Eden.rosewood V.Q (Sn i) d 1=1 from YM.Arise.Pair.emptyW _, map_one] -- order inspect
lemma framePin(v:Label d)(p₀:EuPin)(s:Signed)(h:p₀.Lifts s)(b:Cover): Action.pin p₀ s ⇑((lung V d v) b)= ⇑((lung V d (sym.pin d p₀ v)) (s.act b)):=by
     change Action.pin _ _ ⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ _) _ _) =⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ (sym.pin d p₀ v).val) _ _); rw [sym.pinActs]; exact skies b V.η V.w s p₀ _ V.H V.Q (ncl (i:=i) d V) V.ht V.ha V.ho V.hj h
lemma frameAdj(v:Label d)(a:Axis)(b:Cover): Action.adj a ⇑((lung V d v) b)= ⇑((lung V d (sym.adj d a v)) ((Signed.mirror a).act b)):=by
     change Action.adj a ⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ _) _ _) =⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ (sym.adj d a v).val) _ _); rw [sym.adjActs]; exact spaces b V.η V.w a _ V.H V.Q (ncl (i:=i) d V) V.ht V.ha V.ho V.hj
lemma frameC(v:Label d)(b:Cover): Action.charge ⇑((lung V d v) b)= ⇑((lung V d (sym.charge d v)) b):=by
     change Action.charge ⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ _) _ _) =⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ (sym.charge d v).val) _ _); rw [sym.chargeActs]; exact copES b V.η V.w _ V.H V.Q (ncl (i:=i) d V) V.hj
lemma frameP(v:Label d)(b:Cover): Action.parity ⇑((lung V d v) b)= ⇑((lung V d (sym.parity d v)) b):=by
     change Action.parity ⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ _) _ _) =⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ (sym.parity d v).val) _ _); rw [sym.parityActs]; exact pepper b V.η V.w _ V.H V.Q (ncl (i:=i) d V) V.hj
lemma frameF (u:FlavorTorus)(v:Label d)(b:Cover): Action.flavor u ⇑((lung V d v) b)= ⇑((lung V d (sym.flavor d u v)) b):=by
     change Action.flavor _ ⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ _) _ _) =⇑((lotus d _ _ _ (ncl (i:=i) _ V) _ _ (sym.flavor d u v).val) _ _); rw [sym.flavorActs]; exact fluke b V.η V.w u _ V.H V.Q (ncl (i:=i) d V)
end YM.Intag.Sprig
#check YM.Arise.Pair.emptyW
#print axioms YM.Intag.Sprig.framePin
#print axioms YM.Intag.Sprig.aperture
#print axioms YM.Intag.Sprig.lute
