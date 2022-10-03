import React, {useEffect, useState} from 'react'
import {AppContent, AppSidebar, AppFooter, AppHeader} from '../ui-components/index'
import {Navigate} from "react-router-dom";
import {isLoggedIn} from "../helpers/authHelper";

const DefaultLayout = () => {
    return !isLoggedIn() ? <Navigate to="/login" replace/> : <div>
        <AppSidebar/>
        <div className="wrapper d-flex flex-column min-vh-100 bg-light">
            <AppHeader/>
            <div className="body flex-grow-1 px-3">
                <AppContent/>
            </div>
            {/*<AppFooter />*/}
        </div>
    </div>
}

export default DefaultLayout
