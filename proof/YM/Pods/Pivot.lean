import YM.Pods.Iota
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
abbrev aspect (u: List Axis):= spine Q w u
lemma appSp (v w':List Axis): spine Q w (w'++ v)= spine Q (spine Q w v) w':=by induction w' with| nil =>simp [spine]|cons i l ih=>simp only [List.cons_append,spine,ih]
-- transport backward quota (toward 0), works for ANY v. lifts choose.W circular. T.reflect.V.P.To y
variable (g: Ratio c n) (hG:Odd g.count.val)(he:Even c.val)(W:Site n)
include hu h he hG
local notation "T"=> mural g he W
variable (v: Site c)(b:Cover) (hr:R.t=0)
include hr
-- zero root cost imply any x at matching center. plus SameTile inferred separately.
lemma tackle (ht:wrap n b= (T).copyMap v W) (C:ℝ)(hQ:∀ l:List Axis,l.length ≤8→ ∀ b:Cover,wrap n b=W→floorL T φ R (B b (spine Q w l)) 0≤ C): floorL T φ R (B b w) (show (T).Cell from v) ≤ C:=by
    let t:= T; let v': t.Cell:= v; obtain ⟨P,x,h₀,hX⟩:= chooseMap t v' b
    have hV : t.copyMap v' x=t.copyMap v' W:=(hX _).symm.trans (by rw [h₀,ht]) -- dependent. test
    have he : x=W:= (show Injective (t.copyMap v') from (QCD.Revolve.shiftE (t.omega v') (t.translateBy v')).injective) hV
    -- replace subst?
    obtain ⟨l,hl,hf⟩:= legsT t v' 0
    have hx₂:wrap n (P (0:t.Cell))=W:= (hX _).trans ((point0 t x).trans he)
    let Y:= spine Q w (axes (pathT t l)); have hφ := spirals R A Q h w q hu t v' rfl P (relationG t _ _ hX) hr l
    rw [hf,h₀] at hφ; change floorL t _ _ _ v' ≤ _; rw [due t R rfl hr (B b w) (B (P (0:t.Cell)) Y) v' 0 l hf ⟨q,fade _ _ h w q hu _⟩ ⟨q,fade _ _ h Y q hφ.1 _⟩ hφ.2]
    exact hQ _ (by simpa [axes,pathT] using hl) _ hx₂ -- hQ depends binder any
omit hu h he hG hr
variable (C:Cells.Tiling n)
variable (hC:C.kind=.link)(hb:0 ≤ R.β)(hn:4≤ n.val)(hx:R.average 1=1)
local notation "ε"=> Spiro.homeFor g C
local notation "τ"=> mural g he (Spiro.homeFor g C)
include hG he hu h hr hC hb hn hx
-- Sweep placements. at offsets counted. includes support check home small tile requested all its replicas directly. Sh.A.Scope ambiguity
lemma swept (ho:wrap n b∈ C.chamber 0)(ht:wrap n b∈ Spiro.onCenters g he ε)(hd:g.count.val ∣ C.side.val)(V:ℝ)(hp:0 ≤ V)
 (hQ:∀ l:List Axis,l.length≤16→∀ b:Cover,wrap n b=ε→ floorL τ φ R (B b (spine Q w l)) 0≤ V)
 (hX:∀ l:List Axis,l.length≤8→∀ v:(mural g he (Spiro.homeFor g C)).Cell,∀ b:Cover,wrap n b=(mural g he (Spiro.homeFor g C)).copyMap v ε → Base τ v 0 (B b (spine Q w l)) ) : floorL C φ R (B b w) 0≤ V:=by
    let t:= τ; let y(v:C.Cell):= C.copyMap v (wrap n b)
    choose f hf using fun i:C.Cell=> Spiro.turns g C he hG ht hd i
    have hrT(v):y v=t.copyMap (f v) ε:=hf v
    have hi : Injective f:=by intro i j h; have hxy:y i=y j:=(hrT i).trans (h ▸ (hrT j).symm); exact (C.which_chamber (show y i∈C.chamber i from C.enumerate i ho)).symm.trans (hxy.symm ▸ C.which_chamber (C.enumerate j ho))
    obtain ⟨p,x,h₀,hG'⟩:= chooseMap C 0 b; have hw(b:C.Cell):wrap n (p b)=y b:= (hG' _).trans (congr_arg _ ((point0 C x).symm.trans ((hG' 0).symm.trans (congr_arg _ h₀)))) -- shadow b binder.P.Ok.?
    let F(v:C.Cell):= replicateR C R (B b w) 0 v; choose L hpL hT using (legsT C 0)
    let s (v:C.Cell):= axes (pathT C (L v)); let z(v:C.Cell):= spine Q w (s v)
    let Z(v:C.Cell):= B (p v) (z v); have hP (v) : (s v).length ≤8:=by simpa [s,axes,pathT] using hpL v
    have hY(v:C.Cell):= hX (s v) (hP _) (f v) (p v) ((hw v).trans (hrT v))
    have hΦ (v) := spirals R A Q h w q hu C 0 hC p (relationG C _ _ hG') hr (L v); have hfq(v): SignedEq (F v) (Z v):=by
         have hY:=(hΦ v).2; rw [h₀,hT] at hY; exact ((along C R.zeroCut (B b w) (L v) (0:C.Cell) v ⟨q,fade _ _ h w q hu _⟩ hr hC (hT v)).symm).trans hY
    have hxv(v): floorL t R.average R (Z v) (f v)≤ V:=by
        refine tackle R A Q (z v) q h (hΦ v).1 g hG he ε (f v) (p v) hr ((hw v).trans (hrT v)) V ?_; intro l hl b hB; unfold z; rw [← appSp]; apply hQ (l++s v) _ b hB; have h:= hP v; rw [List.length_append]; omega
    apply le_of_pow_le_pow_left₀ C.cells_positive.ne' hp; rw [roof_power]; let l:= (Finset.univ :Finset C.Cell).toList; change ‖φ ((l.map F).prod)‖ ≤ _; rw [Chess.Fortuna.Array.holds_period R.average (signed_product l _ _ hfq)]
    have hv:= plant t φ R rfl Z f hi 0 l (Finset.nodup_toList _) (by intro i; simp [l]) hY hr (averageSeal t R rfl hb hn 0) hx
    exact hv.trans ((Finset.prod_le_prod (fun i _=>floor_nn t R.average R (Z i) (f i)) (fun i _=>hxv i)).trans_eq (by simp))
end Hub
end YM.Massive.Patria
#print axioms YM.Massive.Patria.Hub.swept
