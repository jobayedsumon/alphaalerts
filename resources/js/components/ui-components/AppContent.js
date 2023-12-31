import React, {Suspense} from 'react'
import {Navigate, Route, Routes} from 'react-router-dom'
import {CContainer, CSpinner} from '@coreui/react'

// routes config
import routes from '../routes'
import {isAdmin} from "../helpers/authHelper";

const AppContent = () => {
    return (
        <CContainer lg className="mt-5">
            <Suspense fallback={<CSpinner color="primary"/>}>
                <Routes>
                    {routes.map((route, idx) => {
                        return (
                            route.element && (!route.admin ?
                                    <Route
                                        key={idx}
                                        path={route.path}
                                        exact={route.exact}
                                        name={route.name}
                                        element={<route.element/>
                                    }
                                    /> : isAdmin() && <Route
                                    key={idx}
                                    path={route.path}
                                    exact={route.exact}
                                    name={route.name}
                                    element={<route.element/>
                                    }
                                />
                            )
                        )

                    })}
                    <Route path="/" element={<Navigate to="discord" replace/>}/>
                </Routes>
            </Suspense>
        </CContainer>
    )
}

export default React.memo(AppContent)
