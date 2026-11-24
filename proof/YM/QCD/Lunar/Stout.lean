import YM.QCD.Lunar.Cable
/-! # Fermi canonical global Moment. native. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Stew
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N:ℕ} {v:Strut c}{k:Spike}{g:Site c→ℂ}
namespace Project
open Revolve Flume Quarry
variable (c)
def stone (j:Bool)(i o:Site c):ℂ:=shine i o* if j then (Entr.crest (o-i):ℂ) else 1
noncomputable def μDir (j:Bool) : Sheet c→L[ℂ]Spike:=LinearMap.toContinuousLinearMap {
   toFun:=fun X=>∑ i,∑ k, stone c j i k • gold (cell X i k), map_add':=fun x y=>by
             simp only [← Finset.sum_add_distrib]; exact sum_congr rfl fun i hi=>sum_congr rfl fun k _=>(show _ from by rw [show gold (cell (x+y) i k)= _ from (show _=gold (cell x i k)+gold (cell y i k) from rfl),smul_add])
   map_smul':=fun i X=>by
             simp only [RingHom.id_apply, Finset.smul_sum]; refine sum_congr rfl fun k _=>sum_congr rfl fun j' _=>?_ ; rw [show gold (cell (i • X) k j')=i • gold (cell X k j') from rfl, smul_comm] }
variable {i j:Site c}{U:Support c}
-- equality with local.Price
lemma pathF (z:Site c) (i j:Walk): shimmer 0 z (i++j)=shimmer 0 z i*shimmer 0 (stop z i) j:=by
   induction i generalizing z with
   | nil=> simp only [shimmer,stop,List.nil_append,one_mul]
   | cons a i ih=>rw [List.cons_append, shimmer,ih,shimmer,mul_assoc]; rfl --edit
lemma jog (x:Cover)(i:Walk): stop x i=x+stop 0 i:=by
   have h(x y:Cover)(i:Walk):stop (x+y) i=x+stop y i:=by induction i generalizing y with
        | nil=>rfl
        | cons a i ih=> rw [stop,add_assoc,ih, stop]
   simpa using h x 0 i
lemma glow (x y o:Site c)(h:Nonwrapping U o)(hx:x∈U)(hy:y∈U): shine o x*shine o y=shine x y:=by
     let p:= route 0 (heel o x) 1; let q:=route 0 (heel x y) 1; have ht: heel x y = heel o y - heel o x:= Lunar.neighL y x h hy hx
     have he: stop (0:Cover) (p++q)=heel o y:=by rw [stop_append,show stop (0:Cover) p=heel o x from route_end .., jog,show stop (0:Cover) q=heel x y from route_end ..,ht]; abel
     have hS: stop o p=x:=by rw [wrap_stop,show stop (0:Cover) p=heel o x from route_end .., wrap_lift]; abel
     rw [shore o y (p++q) he,pathF,hS,show shimmer 0 o p= _ from (show _=Stew.shine o x from rfl),show shimmer 0 x q=Stew.shine x y from rfl,←mul_assoc, show shine o x*shine o x=1 from ?_,one_mul]
     rcases shines o x with h|h<;>simp [h]
noncomputable def localW (j:Bool)(F:SampleX→Spike):Spike:= if j then Entr.Jot F else F none
lemma harvest (i j o: Site c)(ht:Nonwrapping U o)(h:i∈U)(hk:j∈U): stone c true i j = shine o i * shine o j * (mark o (some (0,true)) i j - mark o (some (0,false)) i j):=by
     have hz:=glow c i j o ht h hk; unfold mark stone Entr.crest; rw [Lunar.neighL j i ht hk h]; simp [hz]
lemma uplift (j:Bool)(b:Flavor N)(u:EvenA c N)(hv:Gated U u)(o:Site c)(h:Nonwrapping U o): μDir c j (meter b u)=localW j (shape o (feeF b u)):=by
    let X i k:= stone c j i k • gold (cell (feeF b u) i k); have hz(i k:Site c)(he:i∉U ∨ k∉U): X i k=0:=by unfold X; rw [colour_room u hv b he,gold0,smul_zero]
    have hp : μDir c j (meter b u)=∑ i∈U,∑ k∈U,X i k:=by
         change (∑ i,∑ k,X i k)=_; symm; exact (sum_congr rfl (fun i _=>Finset.sum_subset (subset_univ _) (fun k _ hk=>hz i k (Or.inr hk)))).trans (sum_subset (subset_univ _) fun i _ hi=>sum_eq_zero (fun k _=>hz i k (Or.inl hi)))
    rw [hp]; cases j
    · change _=shape o (feeF b _) none; rw [sluice _ _ _ U o hv]; apply sum_congr rfl; intro i hi; refine sum_congr rfl fun k hk=>?_ ; unfold X stone; rw [← glow c i k o h hi hk]; rfl -- mul-one?
    change _=shape o _ (some _)-shape o _ (some _); simp_rw [sluice _ _ _ U o hv, ← Finset.sum_sub_distrib]; refine sum_congr rfl (fun i hi=> sum_congr rfl fun k hk=>?_); unfold X; rw [harvest c i k o h hi hk,mul_sub,sub_smul]; rfl
end Project
end YM.QCD.Stew
