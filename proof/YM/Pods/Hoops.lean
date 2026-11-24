import YM.Pods.Muffle
import YM.Pods.Walls
import YM.Pods.Rooms
/-! Fixed-run root cost on aligned SMALL offsets within any testing cells.
   Includes a constant number of label reorientation slots regardless of volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
namespace Hub
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Massive.Chess
open Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth TorusPCAC.Geometry Chess.Fortuna
variable {n c:Side}{k d:ℕ}(R:Regulator n 6)
variable (s:Axis)
local notation "φ"=> R.average
local notation "X"=> R.zeroCut
variable (A:Bore d)(Q:RawSym)(w:Label d)(q:Bool)(h:Rubric Q A)(hu:moored w.val q)
local notation "B"=>A n
variable (g: Ratio c n) (hG:Odd g.count.val)(he:Even c.val)(W:Site n)
include hu h he hG
local notation "T"=> mural g he W
variable (v: Site c)(b:Cover) (hr:R.t=0)
include hr
omit hu h he hG hr
variable (C:Cells.Tiling n)
variable (hC:C.kind=.link)(hb:0 ≤ R.β)(hn:4≤ n.val)(hx:R.average 1=1)
local notation "ε"=> Spiro.homeFor g C
local notation "τ"=> mural g he ε
local notation "K!"=> g.count.val/2
include hC hG he h hb hx hn hu hr
lemma extraHop (s:C.Cell)(hm:wrap n b∈ C.margin s (3*g.count.val)) (hd:g.count.val∣ C.side.val)(V:ℝ)(hp:0 ≤ V)
 (hQ:∀ l:List Axis,l.length≤24→∀ b:Cover,wrap n b=ε→ floorL τ φ R (B b (spine Q w l)) 0≤ V)
 (hX:∀ l:List Axis,l.length≤16→∀ v:(mural g he (Spiro.homeFor g C)).Cell,∀ b:Cover,wrap n b=(mural g he (Spiro.homeFor g C)).copyMap v ε → Base τ v 0 (B b (spine Q w l)) )
 (hs:∀ l:List Axis,l.length≤8→∀ b:Cover,wrap n b∈ C.margin 0 (2*g.count.val)→Base C 0 0 (B b (spine Q w l))) : floorL C φ R (B b w) s ≤ V:=by
     obtain ⟨p,x,h₀,hV⟩:= chooseMap C s b; obtain ⟨L,hL,hf⟩:= legsT C s 0
     let W₀:= axes (pathT C L); let y:=spine Q w W₀; have he':W₀.length ≤8:=by simpa [W₀,axes,pathT] using hL
     have hφ := spirals R A Q h w q hu C s hC p (relationG C _ _ hV) hr L; rw [hf,h₀] at hφ; have hY:moored y.val q:= hφ.1
     rw [due C R hC hr (B b w) (B (p 0) y) s 0 L hf ⟨q, fade _ _ h w q hu _⟩ ⟨q,fade _ _ h y q hY _⟩ hφ.2]; apply upperBase C R A Q h hC hr y q hY hb hn (p 0) V g hG he -- sig order.Verify
     · rw [(hV _).trans (point0 C x)]; apply (C.reflected_margin x s _).2; rwa [← hV s,h₀]
     · exact fun b he=> hs _ he' b he
     intro b hb' hw
     refine Hub.swept R A Q y q h hY g hG he b hr C hC hb hn hx hb'.1 hw hd V hp ?_ ?_
     · intro l hl; unfold y; rw [← appSp]; exact hQ _ (by rw [List.length_append]; omega)
     intro l hl; unfold y; rw [← appSp]; exact hX _ (by rw [List.length_append]; omega)
omit hC hG he h hb hx hn hu hr
include he hG
lemma precise (v:(T).Cell) : (T).copyMap v W ∈ (T).margin v (K!) := by
    apply ((T).reflected_margin W v _).mp; let t:= T; have hl:=lies g he hG W; let y:=g.count.val; have hW:y<n.val:=Tiling.narrow t; refine ⟨hl,fun i=>?_⟩
    have hc: t.coordinated 0 W i=y/2:=by unfold Tiling.coordinated; rw [Tiling.starts_zero]; change (W i-(W i-((↑(y/2) : Per n)))).val=y/2; rw [sub_sub_cancel,ZMod.val_natCast_of_lt (by omega)]
    obtain ⟨k,hk⟩:= hG; change (y/2 ≤ t.coordinated 0 W i) ∧ (t.coordinated 0 W i + y/2+1 ≤ y); rw [hc]; change y= _ at hk; omega
omit he hG
-- calibration boundary on fixed run, points.V.Intent. AtALL T.T small.A.Tech
open Plans
variable (Y:Sequence)(Ht:SourceRead.TaperHol){Go:YM.Source.Hol su}(Uv:Massive.Lining.Temper.Collage.Exhibit Go)(base:ℕ→ℕ) (U:Massive.Lining.Temper.Collage.Exhibit.CoreMix)
local notation "P" => Uv.display Y Ht Q U base
local notation "A₀"=> Bloom Uv
variable (v:Cover)
-- fixed stencil.Centered for RPC
include hu
lemma harvest (K:ℕ)(t:C.Cell)(hb: wrap n b∈ C.margin t K)(hp:∀ i∈(Uv.display Y Ht Q U base).stencil d,∀ a:Axis,(i a).natAbs < K)(he:C.kind=.link) : Base C t 0 (A₀ d n b w):=by
    let P':= P; let S:= P'.stencil d; have hP:= Uv.ready Y Ht Q U base
    refine ⟨?_,hP.invariant d n b w, q,fade _ _ (stays Uv Ht Y base Q U d) w q hu _⟩; rw [zero_margin C t he]; exact houses S b _ (fun x ⟨u,hu,h⟩=>h ▸ (C.fits_stencil hb (z:=u) (hp u hu))) _ (P'.localMap d w) (hP.localizes d n b w)
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.extraHop
#print axioms YM.Massive.Patria.Hub.precise
#print axioms YM.Massive.Patria.Hub.harvest
