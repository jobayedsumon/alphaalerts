import React, { useMemo } from "react";
import DataTable, {createTheme} from "react-data-table-component";
import FilterComponent from "./FilterComponent";
import {Link} from "react-router-dom";

createTheme('solarized', {
    text: {
        primary: '#fff',
        secondary: '#fff',
    },
    background: {
        default: '#4e2e6e',
    },
    striped: {
        default: '#5A4377',
    }
}, 'dark');

const CustomTable = (props) => {
    const [filterText, setFilterText] = React.useState("");
    const [resetPaginationToggle, setResetPaginationToggle] = React.useState(
        false
    );
    const filteredItems = props.data.length > 0 ? props.data.filter(
        item =>
            JSON.stringify(item)
                .toLowerCase()
                .indexOf(filterText.toLowerCase()) !== -1
    ) : [];

    const subHeaderComponent = useMemo(() => {
        const handleClear = () => {
            if (filterText) {
                setResetPaginationToggle(!resetPaginationToggle);
                setFilterText("");
            }
        };

        return (
            <div className="d-flex justify-content-between w-100">

                <FilterComponent
                    onFilter={e => setFilterText(e.target.value)}
                    onClear={handleClear}
                    filterText={filterText}
                />

                <div>
                    {props.createLink && <Link to={props.createLink} className="btn btn-primary">Create</Link>}
                </div>



            </div>

        );
    }, [filterText, resetPaginationToggle]);

    return (
        <DataTable
            title={props.title}
            columns={props.columns}
            data={filteredItems}
            defaultSortField="id"
            striped
            pagination
            subHeader
            subHeaderComponent={subHeaderComponent}
            subHeaderAlign="left"
            theme="solarized"
        />
    );
};

export default CustomTable;
