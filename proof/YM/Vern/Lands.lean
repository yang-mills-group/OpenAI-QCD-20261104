import YM.Vern.Vue
set_option maxHeartbeats 580000
set_option autoImplicit false
noncomputable section
namespace YM.Vern
open Function Set Filter Analysis MeasureTheory Lattice QCD QCD.Lat
open Massive Massive.UV Massive.Tarn Massive.Tarn.Choir Massive.Tarn.Choir.Strip Massive.Patria.Gall.Onyx
open Massive.Tarn.ChargeQ Massive.Poised.Plans.Stamp.Stair Massive.Gust
open scoped Topology ContDiff BigOperators Classical ComplexOrder Matrix InnerProductSpace
open Sprig Intag.Sprig UV.Free Massive.Poised.Plans.Stamp Heron Iceberg Lobo
open scoped YM.Iceberg
variable {C:Sequence}{P:Calibration C}{K:Choir}{T:Pollens P K} {φ:ℕ→ℕ}
variable (hf:Foil P K T)(HQ:K.Harmony P φ)(E:Canopy P φ K)(X:Lanterns T E)
variable {d:ℕ}
include hf HQ
noncomputable def haloZ (d:ℕ)(k:ℕ) : Tide (Free.Symbol d):=by
      let r:=(E.B k).r; let F:= entryQ hf HQ timeAxis r (E.B k).realH d; let S:=X.frame k d; refine {knot:=fun x y=> F.knot (S x) (S y), positive:=fun x hx=>F.positive _ (fun h=> hx (S.injective (h.trans S.map_zero.symm))), con:=fun _ _=> F.con ..,add:=fun _ _ _=>?_, sep:=fun c x y=>?_}; · rw [map_add,F.add]
      rw[map_smul,F.sep]
-- limit positive. inherits sesqui
variable (p q:Label d)(v u:Free.Symbol d)
lemma rumor (k:ℕ): (haloZ hf HQ E X d k).knot (projection p) (projection q)= LoomZ T E K.total (fun _ :Fin 2=>d) (![P.sym.adj d timeAxis p,q]) X k scent :=by
     let r:=(E.B k).r; let a:= timeAxis; change K.total 2 (points (![0,r • basis a])) _= _; unfold LoomZ; rw [show (E.B k).r • scent=points (![0,r • basis a]) from ?_]; apply congr_arg; funext i; fin_cases i; exact (X.leaders k d).reflects p a; rfl
     apply PiLp.ext; intro i; fin_cases i <;> simp[scent,a,r]
noncomputable def cape (u v:Free.Symbol d):ℂ:= UV.Free.wick (fun _:Fin 2=>d) scent (![P.sym.adj d timeAxis ((X.base d).liftS u), (X.base d).liftS v])
lemma paths : Tendsto (fun k=> (haloZ hf HQ E X d k).knot u v) atTop (𝓝 (cape E X u v)):=by
    let B:=X.base d; let p:=B.liftS u; let q:=B.liftS v; have h(i:ℕ):(haloZ hf HQ E X d i).knot u v= _ :=Eq.trans (congr_arg₂ _ (B.right u).symm (B.right v).symm) (rumor hf HQ E X p q i); simp_rw[h]; exact Sprig.nourish T E HQ X _ _ _ (Canopy.assay E) (Canopy.reliable HQ) (Canopy.measureE E) _ (DawnS.distinct 1 zero_lt_one)
lemma campP (hv:v≠0): 0< (cape E X v v).re:=by
     let p:=X.base d; have ht: projection (p.liftS v)≠0:=by rw[p.right]; exact hv
     have h:= DawnS.detecting 1 zero_lt_one (p.liftS v) P.sym ht
     change 0< (UV.Free.wick _ _ _).re; exact h.1 -- check syntax
noncomputable def GStar (d:ℕ): Tide (Free.Symbol d):=by
     let F(i):= haloZ hf HQ E X d i; let h(x y:Free.Symbol d):Tendsto (fun k=>(F k).knot x y) atTop (𝓝 (cape E X x y)):= paths hf HQ E X y x; refine {knot:=cape E X,positive:=fun x hx=>campP hf HQ E X x hx,con:=fun x y=>?_,add:=fun x y z=>?_,sep:=fun c x y=>?_}
     · exact tendsto_nhds_unique ((h x y).star.congr' (Eventually.of_forall fun i=>(F i).con ..)) (h y x)
     · exact tendsto_nhds_unique ((h x (y+z)).congr' (Eventually.of_forall fun i=>(F i).add x y z)) ((h x y).add (h x z))
     exact tendsto_nhds_unique ((h x _).congr' (Eventually.of_forall fun i=>(F i).sep c x y)) ((h x y).const_mul c)
end YM.Vern
#print axioms YM.Vern.GStar
