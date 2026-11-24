import YM.Pods.Axes
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable (S:Scheme){C:Sequence} {d:ℕ}
variable (Yv:ℝ) (Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(sym:RawSym)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "cK"=>C.S
local notation "ς" j:arg=>C.S.side (C.R j)
local notation "γ"=>clock cK
local notation "Pκ" => Uv.display C Ht sym U base
local notation "Ψ"=> Bloom Uv
variable (w:Label d)(q:Bool)(hp: moored w.val q)(hw:w ≠0)
-- bounds same fixed reference across all ≤24 rotations, convert budgets.All.Point.R.One.G minimal interior.fit. Y.Opacity.S
variable (hX:(Uv.display C Ht sym U base).System)
variable (hY:Spent C (Uv.display C Ht sym U base))
variable (e:ℝ)(he:0<e)
variable (hs:Sway C.S){β ν:ℝ}(hC:C.Path β ν)
local notation "V₁"=> rayM C.S d e
set_option quotPrecheck false
local notation "Ω" i:arg => (C.A i).regulator
local notation "ℓθ"=> 24
-- Bases.Cumes.
def iris {C:Sequence}(P:Calibration C) (w:Label d)(V:ℝ)(j i:ℕ):Prop:=∀ l:List Axis,l.length≤24→∀ h:j≤ C.N i,let g:= viewW C.S (C.R i) h; ∀ he:Even (C.S.side (C.R i) j).val,∀ b:Cover,floorL (mural g he (wrap _ b)) ((C.A i).regulator.average) (C.A i).regulator (P.physical none i (spine P.sym w l) b) 0 ≤ V
include hX hC
lemma expanse (j d:ℕ) :∀ᶠ i in atTop,∀ (w:Label d)(q:Bool),moored w.val q→ w≠0→∀ v:ℝ, 0≤ v→iris Pκ w v (j+1) i→ wider C Pκ w v j i:=by
   obtain ⟨r,hR⟩:= largeK ((Pκ).stencil d); let G:=Pκ
   filter_upwards [(stamp_big hC (j+1)).eventually_ge_atTop (2*r),hX.mixing d] with i hl he' w q hp hw v hv hi; intro h g T hF hT s b hb
   let f:= C.S.side (C.R i) (C.N i); let V:= Ω i; let x:= (G.mix d none i) w; let p:= v; let C':= C.R i
   let l:=g.count.val
   have hf:2*r ≤ l:=hl; have hQV: l ∣ T.side.val:=⟨_, hF.trans ((step_factor h).trans (mul_comm ..))⟩
   let heo:Even (((ς i) (j+1)).val):= evenW _ _ (hC.even i) _; have hp0: Odd l:= viewOdd _ _ h; let W₀:= Spiro.homeFor g T; let τ:=mural g heo W₀
   let Y:= Ψ d; have hω:= he'.star; let Φ:= G.mix d none i; have hs(l:List Axis):spine sym x l= Φ (spine sym w l):=by induction l with | nil=>rfl| cons a l ih=>rw [spine,ih,spine]; exact hω _ _ _
   have hu₁ : sym.parity d x=Φ ((sym.parity d) w):= by
        have h: (sym.parity d)*(Φ)= Φ*(sym.parity d):= he'.parity none; exact DFunLike.congr_fun h w
   have ht:moored x.val q:= (moored_iff sym _ q).2 (hu₁.trans (by rw [(moored_iff sym w q).1 hp,map_smul]))
   have h₁:x≠0:=fun h=> hw (Φ.injective (h.trans (map_zero Φ).symm)); have hb₀:0 ≤V.β:=(hC.normalized i).beta_pos (Nat.le_refl _) |>.le -- implicit.F n
   refine ⟨harvest sym x q ht b T (n:=f) C Ht Uv base U _ _ hb ?_ hT,?_⟩ -- arg order.Check
   · intro i h a; have hh:=hR i h a; change (i a).natAbs <3*l; omega
   apply extraHop V Y sym x q (stays Uv Ht C base sym U d) ht g hp0 heo b rfl T hT hb₀ (sideW hC i _) (battery hC i) s hb hQV p hv
   · intro u hu b he; rw [hs]; have hΨ:= hi u hu h heo b; change floorL τ V.average V ((Pκ).physical (d:=d) none i (spine sym w u) b) _≤ _
     -- rw at hΨ let expressions.Stage; don't motive.T.Tile.Apply equality between floorL and zero via subst x using lemma.
     let W:= (Pκ).physical none i (spine sym w u) b
     have hm : ∀ x y:Site f, x=y→ floorL (mural g heo x) V.average V W 0=floorL (mural g heo y) V.average V W 0:=by intro x y h; subst y; rfl
     exact (hm _ _ he.symm).trans_le hΨ
   · intro u hu v b hb;
     have hq:=(precise g hp0 heo W₀ v); apply harvest sym _ _ (toured sym x q ht u h₁).1 b τ (n:=f) C Ht Uv base U (l/2) v (hb.symm ▸ hq) _ rfl
     intro y he a; have hY:= hR y he a; omega
   intro u hu b hb'
   apply harvest sym _ _ (toured sym x q ht u h₁).1 b T (n:=f) C Ht Uv base U _ _ hb' _ hT
   intro y he a; have hh:=hR y he a; change (y a).natAbs <2*l; omega
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.expanse
