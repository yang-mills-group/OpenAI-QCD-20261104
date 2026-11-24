import YM.QCD.Jets.Drums
/-! # first dynamical census inside one market. True-support. Inputs finite. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Touch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.AbsoluteSums Footprint Trees
open Sun ConnectedActivityE6 Pressure Animals Garden
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F j k:ℕ}{L:Side} {x u v a b c ν C D T θ w κ q Y ε e z: ℝ} {i m:ℕ}{f g: ℝ→ℝ}

structure Crown (P: Plan j)(F k m:ℕ)(L:Side)(a A b B t e K θ C:ℝ) (l:ℕ)(p η u h r:ℝ):Prop where
 wolf :0<r
 orbit :0<η
 -- all terminal mass here broader allowance. Sun can choose any legal pack. size. Packing space delayed for Mark movers, etc.
 pays : ∀ᶠ x in atTop, let s:= haloK L x; let ζ := coneK L η x; let n:=radiusB x
                        0<s ∧ 0<ζ ∧ ∀ f c : Side, 2*(n+1)< f.val → ∀ (Z:Offer 1 a A)(U:Offer 2 b B)(m₀:ℝ)(J:Flight j k)(H:f.val=c.val*J.L.val), J.L=L→ |m₀|≤s→
                        let T:= pesto P J H (trunkM Z U s m₀ f)
                        Species J H u p ζ r h l T ∧ ∀ X : Sun J c f H ζ u p r h l T,∀ {E V:Type}[Countable E][Countable V], ∀ (R:Rise f F E V)(β:E→ℝ)(Q:V→ℝ)(W:Fj (Tr f) E V→Support c),
                          let d:=X.equip F n
                          let y:= fan L θ x
                          let μ i:= Real.exp 1*terra X F n y (K*y) i
                          let Y:=paidSet d R μ β Q C (cashM L θ x) (taxK L x (1/2)) 1
                          Cents R β Q y (fiery su x L) → Fill R β Q t t (taxK L x 1) 1 (chip L x) (highR L x) → Count d R W → (∀ i,W i⊆ enlargement (sliceL J H) m n (native d R i)) →
                          Peak d (fiery su x L) y (K*y) C μ ∧ 1 ≤ cashM L θ x ∧ 1 ≤ taxK L x (1/2) ∧ Ready W n Y e (fan L (-θ-θ/2) x) 1 (fan L (-θ) x)

/-- Before L for E geometry and h enhancement; actual paths/vertices can pay after L! -/
theorem apparel (P : Plan j) (F k m:ℕ)(hj:4≤ j)(hk:4≤k)(t e K θ ρ:ℝ) (ht:0<t)(he:0≤e)(hK:0<K)(hΘ:0<θ)(hr:0<ρ):∃ i:ℕ,∀ L:Side, i≤L.val→∀ (a b A B:ℝ), 0<a→0<b→0≤A→0≤B→∃ C:ℝ,1≤C ∧ ∃ l p η u h, Crown P F k m L a A b B t e K θ C l p η u h ρ:=by
   let t':= t/4; have ht':0<t':=by unfold t'; positivity
   have he':0≤e+1:=by linarith
   let r := ρ/2; have hr':0<r:=half_pos hr
   let ξ:= r/4; have hξ:0<ξ:=by unfold ξ; positivity
   obtain ⟨n,H⟩:= Fees.exponent m ht' he' (show 2*t'<t by unfold t'; linarith)
   obtain ⟨o,O⟩:= Fees.exponent m hξ he' (show 2*ξ<r by unfold ξ; linarith)
   obtain ⟨n',hd⟩:=dice P F hj hk K hK
   refine ⟨n+o+n',fun L hL a b A B ha hb hA hB=>?_⟩
   obtain ⟨η,m',p,u₀,s,hs,hs',hh,N,hp⟩:=ceremony (a:=a) (d:=b) ha hb hr.le P k L B A
   -- p>0/h>0 SUPPLY Species? ceremony uses ∃ a Sun.. for branch OFFER selection. Need get positivity generally. solve choose pad Offer.zero using generator or weaken conclusions only under any.
   let T:=max 1 (K*fingers F*p)
   have hw:1 ≤ T:=le_max_left ..
   refine ⟨T,hw,N,p,η,m',u₀,hr,hh,?_⟩ -- orbit ordering? shape etc
   filter_upwards [kentucky L hs, hd L (by omega) η ρ p u₀ hh hr N, lets L θ hΘ t 0 e ht K T hK hw 0 t' r p ρ ξ ξ (by unfold r; linarith) F j k m N he (by unfold t'; linarith) ht'] with x h w Q
   intro v z d
   have hv: 0 < v:= h.1
   have hz : 0<z:=mul_pos hh (pow_pos hv _)
   refine ⟨hv,hz,fun f c ht K₁ K₂ y J H' hJ hw'=>?_⟩
   intro M
   have hκ : Species J H' m' p z ρ u₀ N M:=hp N le_rfl K₁ K₂ J c f H' v y hJ hv h.2.1 (hw'.trans h.2.1)
   refine ⟨hκ,fun X E V _ _ R β Q' W=>?_⟩
   obtain ⟨π,hπ,hx⟩:=w c f ht J H' hJ m' a A b B y K₁ K₂ hw' X
   let Y:= sliceL J H'
   have he := H c f Y (show n≤ Y.count.val from (Nat.le_trans (by omega : n ≤ L.val) (show L.val ≤ Y.count.val from le_of_eq (congr_arg _ hJ.symm))))
   have hs:= O c f Y (show o≤ Y.count.val from (Nat.le_trans (by omega : o ≤ L.val) (show L.val ≤ Y.count.val from le_of_eq (congr_arg _ hJ.symm))))
   exact Q _ _ J M hJ H' m' z u₀ X π he (show reserve ρ (e+1) (conversion Y m) ξ from ⟨hs.1,hξ,hs.2.2.trans (by unfold r; linarith)⟩) hs hπ hx (le_max_right ..) R β Q' W
end YM.QCD.Jets.Touch
